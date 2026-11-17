/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Module_depth_quotSMulTop_succ_eq
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
[port] name clash with a declaration already in the repository: renamed `Module.depth` → `Module.depth_c2m`.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_Patching_SystemTypes
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_Module_depth_quotSMulTop_succ_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open IsLocalRing RingTheory
theorem Module.depth_quotSMulTop_succ_eq
    {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]
    {x : R} (hx : x ∈ maximalIdeal R) (hxreg : IsSMulRegular M x) :
    Module.depth_c2m R (QuotSMulTop x M) + 1 = Module.depth_c2m R M := by p2m_exact_reverting @_root_.P2MW.S_Module_depth_quotSMulTop_succ_eq.solution
