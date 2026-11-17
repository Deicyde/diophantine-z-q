/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_exists_derivation_constantFieldExtension_map_mem (git blob c005f87305c8ec9d84e64101a7dc1d89f33b14c7, sha256 a8a5c4e16d54ab071c3f632a4fc2d04736f7d5dde227cfdbcc5780c8f13220f6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_exists_derivation_constantFieldExtension_map_mem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve

theorem AlgebraicCurve.exists_derivation_constantFieldExtension_map_mem
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
    (δ : Derivation K E E) :
    ∃ D : Derivation K FE FE,
      (∀ f : F, D (algebraMap F FE f) = 0) ∧
      (∀ e : E, D (algebraMap E FE e) = algebraMap E FE (δ e)) ∧
      ∀ (P : Place E FE) (z : FE), z ∈ P.toValuationSubring → D z ∈ P.toValuationSubring := by
  revert K F E FE hfg hfgE hgen δ
  exact @_root_.P2MW.S_AlgebraicCurve_exists_derivation_constantFieldExtension_map_mem.solution
