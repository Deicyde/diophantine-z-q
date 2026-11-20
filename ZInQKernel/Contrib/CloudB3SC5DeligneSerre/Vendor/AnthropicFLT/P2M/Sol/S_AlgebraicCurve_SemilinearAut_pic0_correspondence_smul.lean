/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul (git blob 5e5b729a79ce1ba4bf45d6ff483d4526e6f844c1, sha256 4defcc4087e8280a8c75cec8a4bbeaf50db85d3d849bcdb7ae5d5cbe8df501e0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_SemilinearAut_correspondence_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    {g : SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin)
    (hgφ : IntertwinesAlong φ.toRingHom g g') (hgψ : IntertwinesAlong ψ.toRingHom g g')
    (c : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFI hfin hN (g • c)
      = g • Pic0.correspondence φ ψ hφ hψ hFI hfin hN c := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [pic0_smul_mk, Pic0.correspondence_mk, Pic0.correspondence_mk, pic0_smul_mk]
  congr 1
  apply Subtype.ext
  rw [Pic0.coe_degZeroCorrespondence, coe_degZeroSMulHom, coe_degZeroSMulHom,
    Pic0.coe_degZeroCorrespondence]
  exact correspondence_smul φ ψ hφ hψ hgφ hgψ (D : Divisor K F)
