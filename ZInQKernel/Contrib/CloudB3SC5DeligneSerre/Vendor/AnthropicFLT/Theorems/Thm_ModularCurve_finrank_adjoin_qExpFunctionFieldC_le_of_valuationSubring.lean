/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring (git blob 68c9c152c0ea2d27f61957e46235df81f75d9925, sha256 88707cd088ba473750bb20de340ee2a549f85f346b9542f63e23b3ccc51a9d42).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring
    {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    {k : Type*} [Field k] (π : A →+* k)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hF : ∃ t : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ),
      Transcendental L t ∧
        FiniteDimensional
          (IntermediateField.adjoin L
            ({t} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (a b : PowerSeries ℤ)
    (X : ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))
    (hX : (X : LaurentSeries L) = ModularCurve.intSeriesC L a / ModularCurve.intSeriesC L b)
    (x : ModularCurve.qExpFunctionFieldC k Γ)
    (hx : (x : LaurentSeries k) = ModularCurve.intSeriesC k a / ModularCurve.intSeriesC k b)
    (htr : Transcendental k x) :
    FiniteDimensional (IntermediateField.adjoin k ({x} : Set (ModularCurve.qExpFunctionFieldC k Γ)))
        (ModularCurve.qExpFunctionFieldC k Γ) ∧
      Module.finrank (IntermediateField.adjoin k ({x} : Set (ModularCurve.qExpFunctionFieldC k Γ)))
          (ModularCurve.qExpFunctionFieldC k Γ) ≤
        Module.finrank
          (IntermediateField.adjoin L
            ({X} : Set (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ))))
          (ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ Γ)) := by
  revert L A k π Γ hF a b X hX x hx htr
  exact @_root_.P2MW.S_ModularCurve_finrank_adjoin_qExpFunctionFieldC_le_of_valuationSubring.solution
