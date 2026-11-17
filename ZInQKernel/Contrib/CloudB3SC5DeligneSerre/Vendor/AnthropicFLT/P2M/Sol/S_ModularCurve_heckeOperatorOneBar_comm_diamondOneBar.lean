/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_heckeOperatorOneBar_comm_diamondOneBar (git blob 0dac30f18abb1798e5850468aadca44329e26439, sha256 3652f93170397bf3446b00ea3715321beeefd2dc1031b4ecedaeddd233fb799a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_algEquiv_intertwinesAlong_diamondAutBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_heckeOperatorOneBar_comm_diamondOneBar

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.SemilinearAut ModularCurve

theorem solution (M : ℕ) [NeZero M] (ℓ : Nat.Primes) (d : ℕ) :
    ModularCurve.heckeOperatorOneBar M ℓ * ModularCurve.diamondOneBar M d =
      ModularCurve.diamondOneBar M d * ModularCurve.heckeOperatorOneBar M ℓ := by
  haveI hℓ : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  apply LinearMap.ext
  intro x
  simp only [Module.End.mul_apply, heckeOperatorOneBar_apply, diamondOneBar_apply]
  by_cases h : HeckeInputsOneAlong (AlgebraicClosure ℚ) M ℓ
  · obtain ⟨h0, hα, hβ, hP, hfin, hFI, hN⟩ := h
    rw [heckeOperatorOneAlong_eq h0 hα hβ hFI hfin hN]
    obtain ⟨τ, hτα, hτβ⟩ := exists_algEquiv_intertwinesAlong_diamondAutBar M ℓ d
    exact SemilinearAut.pic0_correspondence_smul (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ)
      (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hβ hα hFI hfin hN hτβ hτα x
  · rw [heckeOperatorOneAlong_of_not h]
    simp
