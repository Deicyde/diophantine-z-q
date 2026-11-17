/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_Patching_CohenMacaulayOfDim
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open IsLocalRing

theorem IsLocalRing.IsCohenMacaulayOfDim.ringKrullDim_quotient_add_height
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {d : ℕ}
    (h : IsCohenMacaulayOfDim R d) (p : Ideal R) [p.IsPrime] :
    ringKrullDim (R ⧸ p) + p.height = d := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_IsCohenMacaulayOfDim_ringKrullDim_quotient_add_height.solution
