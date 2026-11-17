/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_FiniteType_exists_notMem_under_forall_trdeg_quotient_le
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_FiniteType_exists_notMem_under_forall_trdeg_quotient_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v

theorem Algebra.FiniteType.exists_notMem_under_forall_trdeg_quotient_le
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
    (𝔮 : Ideal B) [𝔮.IsPrime] :
    ∃ s : A, s ∉ 𝔮.under A ∧ ∀ (𝔔 : Ideal B) [𝔔.IsPrime], 𝔮 ≤ 𝔔 → s ∉ 𝔔.under A →
      Algebra.trdeg (A ⧸ 𝔔.under A) (B ⧸ 𝔔) ≤ Algebra.trdeg (A ⧸ 𝔮.under A) (B ⧸ 𝔮) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FiniteType_exists_notMem_under_forall_trdeg_quotient_le.solution
