/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Pic0_correspondence_correspondence_comm (git blob cea1de10a3adeeda2a3144c1964004a3e0306d03, sha256 01c1fa7fbafd9fc45ae5d5f6ad47e283d93c04dd8ebd2cfa4201a59643473f92).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Pic0_correspondence_correspondence_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.correspondence_correspondence_comm {K F F₁ F₂ : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂] (φ ψ : F →ₐ[K] F₁) (φ' ψ' : F →ₐ[K] F₂) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin) (hFI' : FundamentalIdentityAlong K φ' hφ') (hfin' : FiniteAlong K ψ') (hN' : NormFormulaAlong K ψ' hfin') (hcomm : ∀ D : Divisor K F, Divisor.correspondence φ ψ hφ hψ (Divisor.correspondence φ' ψ' hφ' hψ' D) = Divisor.correspondence φ' ψ' hφ' hψ' (Divisor.correspondence φ ψ hφ hψ D)) (x : Pic0 K F) : Pic0.correspondence φ ψ hφ hψ hFI hfin hN (Pic0.correspondence φ' ψ' hφ' hψ' hFI' hfin' hN' x) = Pic0.correspondence φ' ψ' hφ' hψ' hFI' hfin' hN' (Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) := by
  revert K F F₁ F₂ φ ψ φ' ψ' hφ hψ hφ' hψ' hFI hfin hN hFI' hfin' hN' hcomm x
  exact @_root_.P2MW.S_AlgebraicCurve_Pic0_correspondence_correspondence_comm.solution
