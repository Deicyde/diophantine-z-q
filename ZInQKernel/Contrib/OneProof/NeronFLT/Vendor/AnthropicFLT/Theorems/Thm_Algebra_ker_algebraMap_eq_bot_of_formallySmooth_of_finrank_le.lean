/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open TensorProduct

universe u

theorem Algebra.ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le
    {k P S : Type u} [Field k] [CommRing P] [CommRing S] [IsLocalRing P] [IsLocalRing S] [IsNoetherianRing P]
    [Algebra k P] [Algebra k S] [Algebra P S] [IsScalarTower k P S]
    [Algebra.FormallySmooth k P] [Algebra.FormallySmooth k S] [Module.Finite P Ω[P⁄k]]
    (hPS : Function.Surjective (algebraMap P S))
    (hrank : Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField S ⊗[S] (S ⊗[P] Ω[P⁄k])) ≤
      Module.finrank (IsLocalRing.ResidueField S) (IsLocalRing.ResidueField S ⊗[S] Ω[S⁄k])) :
    RingHom.ker (algebraMap P S) = ⊥ := by p2m_exact_reverting @_root_.P2MW.S_Algebra_ker_algebraMap_eq_bot_of_formallySmooth_of_finrank_le.solution
