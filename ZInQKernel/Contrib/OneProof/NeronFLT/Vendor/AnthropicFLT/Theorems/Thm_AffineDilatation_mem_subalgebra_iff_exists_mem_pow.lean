/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AffineDilatation_mem_subalgebra_iff_exists_mem_pow
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_RingTheory_AffineDilatation
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

theorem AffineDilatation.mem_subalgebra_iff_exists_mem_pow
    {A : Type u} [CommRing A] (I : Ideal A) (a : A) (ha : a ∈ I) (x : Localization.Away a) :
    x ∈ AffineDilatation.subalgebra I a ↔
      ∃ (n : ℕ) (g : A), g ∈ I ^ n ∧
        IsLocalization.mk' (Localization.Away a) g (⟨a ^ n, n, rfl⟩ : Submonoid.powers a) = x := by p2m_exact_reverting @_root_.P2MW.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow.solution
