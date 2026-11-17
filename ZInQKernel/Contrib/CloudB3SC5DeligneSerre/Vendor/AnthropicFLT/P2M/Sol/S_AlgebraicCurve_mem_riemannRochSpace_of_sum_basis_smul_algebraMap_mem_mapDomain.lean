/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain (git blob ac99daeeb7e62801c8d22ded02ab7767adcbfb18, sha256 7c6c1d570efbeeee1137efbc1ab705c009fcd594b54c5fb2e7c7ee964b313e1b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain

set_option autoImplicit false
set_option maxHeartbeats 4000000

open AlgebraicCurve

theorem solution
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift)
    (D : Divisor K F) {ι : Type*} (B : ι → K') (hB : LinearIndependent K B)
    (g : ι →₀ F)
    (hmem : (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j))
      ∈ LSpace (K := K') (Finsupp.mapDomain lift D)) :
    ∀ j, g j ∈ LSpace (K := K) D := by
  classical
  intro j₀
  rcases eq_or_ne (g j₀) 0 with hj0 | hj0
  · rw [hj0]; exact zero_mem _
  have hj0supp : j₀ ∈ g.support := Finsupp.mem_support_iff.mpr hj0
  have hgne : g ≠ 0 := fun h => hj0 (by rw [h]; rfl)
  refine mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)
  obtain ⟨hne, hle⟩ :=
    Place.ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension
      K F K' F' hfg hfg' hgen lift hlift_ord v B hB g hgne
  have hordSig : -(Finsupp.mapDomain lift D) (lift v) ≤
      (lift v).ord (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j)) :=
    (mem_lSpace_iff_ord.mp hmem).resolve_left hne (lift v)
  rw [Finsupp.mapDomain_apply_of_injective hlift_inj] at hordSig
  exact hordSig.trans (hle j₀ hj0supp)
