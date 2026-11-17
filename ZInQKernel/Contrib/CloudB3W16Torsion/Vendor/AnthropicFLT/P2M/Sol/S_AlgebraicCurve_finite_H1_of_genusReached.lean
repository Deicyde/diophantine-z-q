/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_finite_H1_of_genusReached. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_mem_adeleSpace_iff_mem_repartitions
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_mem_repartitionsOf_iff_coe_mem_adeleBdd
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_finite_H1_of_genusReached

set_option autoImplicit false

open AlgebraicCurve in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (D : Divisor K F) :
    Module.Finite K (H1 D) := by
  obtain ⟨hfin, -⟩ := indexOfSpecialty_eq_of_genusReached h D
  let e : ↥(adeleSpace K F) →ₗ[K] ↥(repartitions K F) :=
    { toFun := fun a => ⟨(a : Place K F → F), mem_adeleSpace_iff_mem_repartitions.mp a.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let φ : ↥(adeleSpace K F) →ₗ[K] H1 D := (repartitionsOf D ⊔ principalRepartitions K F).mkQ ∘ₗ e
  have hφ : Function.Surjective φ := by
    intro q
    obtain ⟨β, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨⟨(β : Place K F → F), mem_adeleSpace_iff_mem_repartitions.mpr β.2⟩, ?_⟩
    rfl
  have hker : adeleBddPrincipal K F D ≤ LinearMap.ker φ := by
    refine sup_le ?_ ?_
    · intro a ha
      rw [LinearMap.mem_ker]
      show Submodule.Quotient.mk (e a) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_left (mem_repartitionsOf_iff_coe_mem_adeleBdd.mpr ha)
    · intro a ha
      rw [LinearMap.mem_ker]
      show Submodule.Quotient.mk (e a) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨f, hf⟩ := LinearMap.mem_range.mp ha
      refine Submodule.mem_sup_right (mem_principalRepartitions_iff.mpr ⟨f, ?_⟩)
      funext v
      have hv := congrFun hf v
      rw [diagonalHom_apply] at hv
      exact hv.symm
  have hψ : Function.Surjective ((adeleBddPrincipal K F D).liftQ φ hker) := by
    intro q
    obtain ⟨a, rfl⟩ := hφ q
    exact ⟨Submodule.Quotient.mk a, rfl⟩
  exact Module.Finite.of_surjective _ hψ
