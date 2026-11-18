import InertiaFixedPointFieldV003
import InertiaUnramifiedAtV001

/-!
# Inertia-fixed points of an abelian variety are defined over fields unramified at `w`

For the kernel's abelian variety `A` over a number field `K`, a discrete valuation subring `O`, an
algebraic closure `Ω` and a valuation subring `w` of `Ω` above `O`: an `Ω`-point fixed by every
element of the inertia subgroup of `w` comes from a point over a finite intermediate field `M`
such that the integral closure of `O` in `M` is unramified over `O` at the center of `w`
(`Algebra.IsUnramifiedAt`).
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace InertiaPointDescent

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

theorem exists_unramified_point_field (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K)
    (x : A.Pt Ω) (hx : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → A.galAct σ x = x) :
    ∃ M : IntermediateField K Ω, ∃ _ : FiniteDimensional K M,
      M ≤ IntermediateField.fixedField (inertiaGroup (K := K) w) ∧
      (∃ y : A.Pt M, Spec.map (CommRingCat.ofHom M.val.toRingHom) ≫ y.left = x.left) ∧
      letI : Algebra O M := ((algebraMap K M).comp (algebraMap O K)).toAlgebra
      haveI : IsScalarTower O K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
      Algebra.IsUnramifiedAt O (integralCenter O w hw M.val) := by
  obtain ⟨M, hfd, hfix, y, hy, -⟩ := exists_inertia_fixed_point_field w A x hx
  refine ⟨M, hfd, hfix, ⟨y, hy⟩, ?_⟩
  let _ : Algebra O M := ((algebraMap K M).comp (algebraMap O K)).toAlgebra
  have : IsScalarTower O K M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine isUnramifiedAt_integralCenter O w hw M.val (fun m σ hσ => ?_)
  have hm := hfix m.2
  rw [IntermediateField.mem_fixedField_iff] at hm
  exact hm σ ((mem_inertiaGroup_iff w σ).2 hσ)

end InertiaPointDescent
