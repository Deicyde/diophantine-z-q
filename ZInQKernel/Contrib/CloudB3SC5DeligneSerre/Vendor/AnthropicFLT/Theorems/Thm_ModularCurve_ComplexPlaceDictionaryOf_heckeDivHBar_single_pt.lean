/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt (git blob 677ff0b1dc826a987473a53e362db15f1c2e68cd, sha256 f0eb3f34f65bbea66876dd4a3bb095b959c1c78078580e850e446d2dc763969f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHHeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open UpperHalfPlane in
open scoped MatrixGroups in

theorem ModularCurve.ComplexPlaceDictionaryOf.heckeDivHBar_single_pt
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (h0 : ModularCurve.HeckeBetaHDefined M H ℓ)
    (hα : ModularCurve.HeckeAlphaHBarIntegral ℂ M H ℓ) (hβ : ModularCurve.HeckeBetaHBarIntegral ℂ M H ℓ)
    [AlgebraicCurve.HasPrincipalDivisors ℂ
      (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)))]
    (τ : UpperHalfPlane) :
    (∀ (hℓM : ¬ ℓ ∣ M) (ρ : CongruenceSubgroup.Gamma0 M), (((ρ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ →
      ModularCurve.heckeDivHBar hα hβ (Finsupp.single (D.pt τ) 1) =
        ∑ j ∈ Finset.range ℓ, Finsupp.single (D.pt (ModularForm.heckeMatrix ℓ j • τ)) 1 +
          Finsupp.single (D.pt (((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) *
            ModularForm.heckeDiagMatrix ℓ) • τ)) 1) ∧
    (ℓ ∣ M →
      ModularCurve.heckeDivHBar hα hβ (Finsupp.single (D.pt τ) 1) =
        ∑ j ∈ Finset.range ℓ, Finsupp.single (D.pt (ModularForm.heckeMatrix ℓ j • τ)) 1) := by
  revert M H D ℓ hℓ h0 hα hβ τ
  exact @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_heckeDivHBar_single_pt.solution
