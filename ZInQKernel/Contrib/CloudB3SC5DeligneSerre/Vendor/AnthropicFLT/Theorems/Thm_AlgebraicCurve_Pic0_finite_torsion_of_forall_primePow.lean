/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow (git blob 941ded59e4fd625543bd32d324c51e2f488533b8, sha256 2e1bab66187122134e7ec3d96e2a8922d45c288da094145b3c08d77e3f7a6f71).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.finite_torsion_of_forall_primePow {K F : Type*} [Field K] [Field F] [Algebra K F]
    (h : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), Finite (Pic0.torsion K F (p ^ k))) (n : ℕ) (hn : 0 < n) :
    Finite (Pic0.torsion K F n) := by
  revert K F h n hn
  exact @_root_.P2MW.S_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow.solution
