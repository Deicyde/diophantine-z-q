import ZInQKernel.OneProof.H.TailZ24
import ZInQKernel.Contrib.OneProof.SmoothRegular.Basic

/-!
# smooth-regular: `T09Pic.PicZeroAbVar` from its nonsingular (printed-hypothesis) form

Task smooth-regular (2026-11-16). Report: `docs/research/smooth-regular.md`; log: `scratch/smooth-regular/log.md`.

The open field `HDec.HSyn.OpenAddedLeaves17.picZeroAbVar` (statement `T09Pic.PicZeroAbVar`,
`ZInQKernel/OneProof/H/TailZ24.lean`) asks for `B : PkgI3.AbVar K`, whose structure map is Mathlib's `Smooth`.
The print (Mumford, *Abelian varieties*, §13, over an algebraically closed field) says that `Pic⁰` is an abelian
variety in Mumford's sense: a complete group variety, nonsingular (Mumford §4: group varieties are nonsingular).
`PicZeroAbVarNonsingular` states the same leaf with "smooth" replaced by "nonsingular over `K̄`" (the local rings of
`B ×_K K̄` at closed points are regular local rings), and `picZeroAbVar_of_nonsingular` proves the original from it by
the theorem `smooth_of_nonsingularAfter_algebraicClosure` (`SmoothRegular/Basic.lean`: Stacks 00TV over the perfect
field `K̄`, then fpqc descent of smoothness along `Spec K̄ → Spec K`). `picZeroAbVarNonsingular_of_picZeroAbVar`
proves the converse, so the two statements are equivalent.

No `sorry`, no `axiom`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory Opposite
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.SmoothRegular

/-- **LEAF L2, nonsingular form (`Pic⁰_{A/K}` is an abelian variety).** For every representation `rep` of the
Picard functor of an abelian variety `A/K`, there is a proper, geometrically integral group scheme `B/K` that is
nonsingular over `K̄` (the local rings of `B ×_K K̄` at its closed points are regular), with an open immersion
`j : B → P` onto the identity component of `P` that is a homomorphism for the group law of `rep`. This is
`T09Pic.PicZeroAbVar` with `Smooth` replaced by Mumford's "nonsingular" over `K̄`; same sources: Mumford,
*Abelian varieties*, §13 (`Â = Pic⁰` is an abelian variety, over `K̄`) with §4 (group varieties are nonsingular);
Kleiman, *The Picard scheme*, Prop. 9.5.3 and 9.5.1 (descent to `K`); SGA 3 VI_A 2.4 (geometric connectedness of the
identity component); Milne 1986, §9-10. Numbers UNVERIFIED. -/
def PicZeroAbVarNonsingular : Prop :=
  ∀ (K : Type) [Field K] (A : PkgI3.AbVar K) (P : Over (Spec (CommRingCat.of K)))
    (rep : (picardFunctor A.X.hom).obj.RepresentableBy P),
    ∃ (B : Over (Spec (CommRingCat.of K))) (_ : GrpObj B) (_ : IsProper B.hom)
      (_ : GeometricallyIntegral B.hom), NonsingularAfter B.hom (AlgebraicClosure K) ∧
      ∃ j : B ⟶ P, letI := picardFunctorCommGrpObj A.X.hom rep
        IsOpenImmersion j.left ∧ Set.range j.left = T09Pic.identityComponent P ∧ IsMonHom j

/-- **`T09Pic.PicZeroAbVar` from its nonsingular form** (glue: nonsingular over `K̄` ⇒ smooth). -/
theorem picZeroAbVar_of_nonsingular (h : PicZeroAbVarNonsingular) : T09Pic.PicZeroAbVar := by
  intro K _ A P rep
  obtain ⟨B, _, _, _, hB, j, hj⟩ := h K A P rep
  exact ⟨abVarOfNonsingularAfter B hB, j, hj⟩

/-- The converse: the two forms are equivalent. -/
theorem picZeroAbVarNonsingular_of_picZeroAbVar (h : T09Pic.PicZeroAbVar) : PicZeroAbVarNonsingular := by
  intro K _ A P rep
  obtain ⟨B, j, hj⟩ := h K A P rep
  exact ⟨B.X, inferInstance, inferInstance, inferInstance, nonsingularAfter_of_smooth B.X.hom _, j, hj⟩

end ZInQ.Contrib.SmoothRegular
