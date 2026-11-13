import Mathlib

/-!
# rv-blueprints: the existential R16 is invariant under isomorphism of the Jacobian (repair M1)

Mathlib only. Supports finding M1 of `docs/research/rv-blueprints.md` §2.3: bp-modcurves' leaf
MC9 ("our model of `X₁(N)` is Shimura's canonical model") is not needed, because the existential
R16 transfers along isomorphisms of `J`. The file declares exactly three things, in the namespace
`BPModCurves`:

* `AbVar K` : an abelian variety over a field `K`, i.e. a group object in schemes over `Spec K`
  whose structure morphism is proper, smooth and geometrically integral (copied from the
  repository's `PkgI3.AbVar`, `scratch/pkg-I3/I3.lean`, since scratch files cannot import each
  other).
* the instance `IsCommMonObj A.X` for `A : AbVar K` (an abelian variety is commutative), from
  Mathlib's `isCommMonObj_of_isProper_of_geometricallyIntegral`.
* `exists_quotient_transfer` (glue, proved): if `J ≅ J'` (with `e.inv` a monoid morphism) and some
  surjective homomorphism `J → A` onto an abelian variety `A` satisfying `P A` exists, then one
  exists from `J'` (compose with `e.inv`).

No `sorry`, no `axiom`; no curves, Jacobians or Albanese predicates are defined here (those are in
`Audit_Jacobian.lean`, from which this header was earlier copied by mistake; notes-fix2, issue #2
item 6).
-/

namespace BPModCurves

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

universe u

/-- (Copied from `PkgI3.AbVar`.) An abelian variety over a field `K`: a group object in schemes
over `Spec K` whose structure morphism is proper, smooth and geometrically integral. -/
structure AbVar (K : Type u) [Field K] where
  X : Over (Spec (CommRingCat.of K))
  [grp : GrpObj X]
  [proper : IsProper X.hom]
  [smooth : Smooth X.hom]
  [geomInt : GeometricallyIntegral X.hom]

attribute [instance] AbVar.grp AbVar.proper AbVar.smooth AbVar.geomInt

instance {K : Type u} [Field K] (A : AbVar K) : IsCommMonObj A.X :=
  isCommMonObj_of_isProper_of_geometricallyIntegral A.X

variable {K : Type u} [Field K]

/-- **Transfer of an existential R16-type conclusion along an isomorphism of abelian varieties.**
`P A` stands for every clause of the existential R16 that concerns only the quotient `A` (the
`K_f`-action on `A`, `dim A = [K_f:ℚ]`, the Frobenius traces on the components of `V_ℓ(A)`):
none of them mentions `J`. Hence if the conclusion holds for one Jacobian `J` of one `ℚ`-model of
`X₁(N)`, it holds for every abelian variety isomorphic to `J`, in particular for the Jacobian of
any `ℚ`-isomorphic model. This is why bp-modcurves' leaf MC9 is not needed. -/
theorem exists_quotient_transfer (J J' : AbVar K) (e : J.X ≅ J'.X) [IsMonHom e.inv]
    (P : AbVar K → Prop)
    (h : ∃ (A : AbVar K) (π : J.X ⟶ A.X), IsMonHom π ∧ Surjective π.left ∧ P A) :
    ∃ (A : AbVar K) (π : J'.X ⟶ A.X), IsMonHom π ∧ Surjective π.left ∧ P A := by
  obtain ⟨A, π, hπ, hs, hP⟩ := h
  refine ⟨A, e.inv ≫ π, ?_, ?_, hP⟩
  · have := hπ; infer_instance
  · rw [Over.comp_left]
    have : IsIso e.inv.left := inferInstance
    exact (Surjective.comp_iff (f := e.inv.left) (g := π.left)).2 hs

end BPModCurves

#print axioms BPModCurves.exists_quotient_transfer
