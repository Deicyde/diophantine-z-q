import Mathlib

/-!
# rv-blueprints: the existential R16 is invariant under isomorphism of the Jacobian (repair M1)

Over Mathlib schemes and the repository's `PkgI3.AbVar` (copied below from
`scratch/pkg-I3/I3.lean`, since scratch files cannot import each other: the structure, the
commutativity instance, and nothing else).

* `IsCurve X` : `X → Spec K` is proper, smooth of relative dimension 1, geometrically connected.
* `IsJacobian X P₀ J aj` : `aj : X → J` sends `P₀` to `0`, and every `K`-morphism `f : X → A` to an
  abelian variety with `f(P₀) = 0` factors as `φ ∘ aj` for a unique homomorphism `φ : J → A`
  (the Albanese property; for a curve the Albanese variety is the Jacobian: Milne, *Jacobian
  varieties*, in Arithmetic Geometry (1986), Prop. 6.1, UNVERIFIED number).
* `JacobianExists K` : the existence leaf (Weil 1948; Chow; Milne 1986, Thm 1.1 with Prop. 6.1,
  UNVERIFIED numbers). This is a **leaf statement** (a `Prop`), not proved here.
* `IsJacobian.unique` : any two Jacobians of `(X, P₀)` are isomorphic by a unique homomorphism
  compatible with `aj` (glue, proved). This is the acceptance test for the predicate.
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
