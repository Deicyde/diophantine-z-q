/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Pic0_correspondence_correspondence_comm (git blob 19ec83a343172fd9d99e9546634eb3f6798097b7, sha256 3b6c1e1e05425f20f809066549a0b7af71b17c81d622f9381f54a15514501bbf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Pic0_correspondence_correspondence_comm

set_option autoImplicit false

open IsDedekindDomain AlgebraicCurve

theorem solution {K F F₁ F₂ : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂] (φ ψ : F →ₐ[K] F₁) (φ' ψ' : F →ₐ[K] F₂) (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ) (hN : NormFormulaAlong K ψ hfin) (hFI' : FundamentalIdentityAlong K φ' hφ') (hfin' : FiniteAlong K ψ') (hN' : NormFormulaAlong K ψ' hfin') (hcomm : ∀ D : Divisor K F, Divisor.correspondence φ ψ hφ hψ (Divisor.correspondence φ' ψ' hφ' hψ' D) = Divisor.correspondence φ' ψ' hφ' hψ' (Divisor.correspondence φ ψ hφ hψ D)) (x : Pic0 K F) : Pic0.correspondence φ ψ hφ hψ hFI hfin hN (Pic0.correspondence φ' ψ' hφ' hψ' hFI' hfin' hN' x) = Pic0.correspondence φ' ψ' hφ' hψ' hFI' hfin' hN' (Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.correspondence_mk, Pic0.correspondence_mk, Pic0.correspondence_mk, Pic0.correspondence_mk]
  exact congrArg Pic0.mk (Subtype.ext (hcomm (D : Divisor K F)))
