/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place (git blob b6259f21e14e3c995f4a560ba9b90a20244aafe1, sha256 6c1132a71b077c5f1e4d60caa74040bda1b91d655204d5e521196fbf5d2ca188).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_SemilinearAut_ofAlgAut_smul_place

open scoped Pointwise

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (σ : F ≃ₐ[K] F) (v : AlgebraicCurve.Place K F) : AlgebraicCurve.SemilinearAut.ofAlgAut σ • v = σ • v := by
  have hfun : ∀ x : F, AlgebraicCurve.SemilinearAut.ofAlgAut σ • x = σ • x := fun _ => rfl
  apply AlgebraicCurve.Place.toValuationSubring_injective
  ext x
  rw [AlgebraicCurve.SemilinearAut.smul_toValuationSubring, AlgebraicCurve.Place.smul_toValuationSubring,
    ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  simp only [hfun]
