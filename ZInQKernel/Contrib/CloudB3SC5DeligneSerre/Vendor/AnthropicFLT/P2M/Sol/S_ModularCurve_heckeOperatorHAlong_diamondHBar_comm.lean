/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_heckeOperatorHAlong_diamondHBar_comm (git blob 38c10e49d1edc76c533512eca501901cbb7191f9, sha256 2216fe8ba15ef596db7c5168dffa6988f9ca76ff109261d91d2ec57f5f8dc942).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutHBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_heckeOperatorHAlong_diamondHBar_comm

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.SemilinearAut ModularCurve

theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [Fact ℓ.Prime] (d : (ZMod M)ˣ) (P : ModularCurve.JH M H) :
    ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ (ModularCurve.diamondHBar M H d P) =
      ModularCurve.diamondHBar M H d
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ P) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  rw [diamondHBar_apply, diamondHBar_apply]
  by_cases h : HeckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ
  · obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := h
    rw [heckeOperatorHAlong_eq h0 hα hβ hFI hfin hN]
    obtain ⟨τ, hτα, hτβ⟩ := exists_algEquiv_intertwinesAlong_diamondAutHBar M H ℓ d
    exact SemilinearAut.pic0_correspondence_smul (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ)
      (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hβ hα hFI hfin hN hτβ hτα P
  · rw [heckeOperatorHAlong_of_not h]
    simp
