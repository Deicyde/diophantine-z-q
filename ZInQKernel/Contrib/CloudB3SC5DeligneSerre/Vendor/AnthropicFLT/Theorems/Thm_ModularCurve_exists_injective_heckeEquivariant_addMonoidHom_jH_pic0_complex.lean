/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex (git blob 2709ec86d7f45d3c2eacc7f16bb8ffc8d4d63112, sha256 bfd8113f2b660cc5aa531e6d1fa4f4d94bf280ccdecdbf2b3919ac4e7665aa40).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHHeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_GaloisRep_ComplexConjugation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    ∃ (φ : ↥(ModularCurve.xHFunctionFieldBar M H) →+*
          ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)))
      (ι : ModularCurve.JH M H →+
          AlgebraicCurve.Pic0 ℂ ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))),
      (∀ y : ↥(ModularCurve.xHFunctionFieldBar M H),
        ((φ y : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))) : LaurentSeries ℂ) =
          ModularCurve.coeffMap (complexEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] ℂ).toRingHom
            (y : LaurentSeries (AlgebraicClosure ℚ))) ∧
      Function.Injective ι ∧
      (∀ z, IsOfFinAddOrder z → z ∈ ι.range) ∧
      (∀ (ℓ : ℕ) [NeZero ℓ],
        ModularCurve.HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ →
        ModularCurve.HeckeInputsHAlong ℂ M H ℓ →
        ∀ x : ModularCurve.JH M H,
          ι (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ x) =
            ModularCurve.heckeOperatorHAlong ℂ M H ℓ (ι x)) ∧
      (∀ (g : AlgebraicCurve.SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H))
        (g' : AlgebraicCurve.SemilinearAut ℂ
          ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))),
        (∀ y : ↥(ModularCurve.xHFunctionFieldBar M H), g' • φ y = φ (g • y)) →
        ∀ x : ModularCurve.JH M H, ι (g • x) = g' • ι x) ∧
      ∀ σ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H),
        ∃ σ' : ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) ≃ₐ[ℂ]
            ↥(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)),
          ∀ y : ↥(ModularCurve.xHFunctionFieldBar M H), σ' (φ y) = φ (σ y) := by
  revert M H
  exact @_root_.P2MW.S_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex.solution
