/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_Patching_CohenMacaulayOfDim
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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

def IsCohenMacaulayOfDim (d : ℕ) : Prop :=
  ringKrullDim R = d ∧ Module.depth_c2m R R = d

namespace IsCohenMacaulayOfDim

variable {R} {d : ℕ}

lemma ringKrullDim_eq (h : IsCohenMacaulayOfDim R d) : ringKrullDim R = d := h.1

lemma depth_eq (h : IsCohenMacaulayOfDim R d) : Module.depth_c2m R R = d := h.2

end IsCohenMacaulayOfDim

end IsLocalRing
