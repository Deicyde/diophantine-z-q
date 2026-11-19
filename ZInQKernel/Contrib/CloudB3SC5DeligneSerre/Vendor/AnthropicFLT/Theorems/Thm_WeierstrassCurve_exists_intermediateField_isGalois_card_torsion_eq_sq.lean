/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq (git blob 9ae320da5e8023288bf015bf2255295d1d30357e, sha256 df77f49aa7bbd061f0e9ceb9b5cd78b055679a98ffcfa345f99d9fca2c33ba9e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open WeierstrassCurve WeierstrassCurve.Affine

universe u v in

theorem WeierstrassCurve.exists_intermediateField_isGalois_card_torsion_eq_sq
    {F : Type u} {Ω : Type v} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic F Ω] [DecidableEq Ω]
    (E : WeierstrassCurve F) [E.IsElliptic] {n : ℕ} (hn : (n : F) ≠ 0) :
    ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      Nat.card {P : (E.baseChange L).toAffine.Point // n • P = 0} = n ^ 2 ∧
      ∀ σ : L ≃ₐ[F] L,
        (∀ P : (E.baseChange L).toAffine.Point, n • P = 0 → Point.map (σ : L →ₐ[F] L) P = P) →
        σ = 1 := by
  revert F Ω E n hn
  exact @_root_.P2MW.S_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq.solution
