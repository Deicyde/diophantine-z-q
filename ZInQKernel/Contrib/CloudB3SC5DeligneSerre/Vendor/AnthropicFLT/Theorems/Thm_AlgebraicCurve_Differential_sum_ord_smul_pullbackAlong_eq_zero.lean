/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero (git blob bbcf3c8aca677dcface474a51d68e1a81c747593, sha256 5fd6eb760c6cd378cb40062123893e962d50cc2b1729fc39654fe1d5a9f58d9f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DifferentialPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.Differential.sum_ord_smul_pullbackAlong_eq_zero
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE]
    [Algebra K F] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    [IsCurveOver K F] [IsCurveOver E FE]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (g : FE) (hg : g ≠ 0)
    (S : Finset (Place E FE)) (y : Place E FE → (F →ₐ[K] E))
    (hS : ∀ P ∈ S, ∀ f : F,
      P.toValuationSubring.valuation (algebraMap F FE f - algebraMap E FE (y P f)) < 1)
    (hrat : ∀ P : Place E FE, P ∉ S → P.ord g ≠ 0 →
      ∃ f : F, algebraMap F FE f ∉ P.toValuationSubring)
    (ω : Ω[F⁄K]) (hω : ω ∈ regularDifferentials K F) :
    ∑ P ∈ S, (P.ord g) • Differential.pullbackAlong (y P) ω = 0 := by
  revert K F E FE hfg hfgE hgen g hg S y hS hrat ω hω
  exact @_root_.P2MW.S_AlgebraicCurve_Differential_sum_ord_smul_pullbackAlong_eq_zero.solution
