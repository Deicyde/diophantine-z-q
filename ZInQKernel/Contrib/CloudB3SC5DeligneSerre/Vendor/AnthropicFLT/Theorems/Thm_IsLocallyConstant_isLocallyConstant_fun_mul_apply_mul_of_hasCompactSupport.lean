/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsLocallyConstant_isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport (git blob 0130faee804ec25f555f0acdad6f9e310db7e6e3, sha256 abc57c0581bee313258f7c553b72521d5cd8ea77c099fc706f988453a5139514).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.LocallyConstant.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_IsLocallyConstant_isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem IsLocallyConstant.isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {Y : Type*} [Zero Y]
    {f : G → Y} (hf : IsLocallyConstant f) (hsupp : HasCompactSupport f) {S : Type*} (n : S → G) :
    IsLocallyConstant (fun kk : G × G => fun s => f (kk.1 * n s * kk.2)) := by
  revert G Y f hf hsupp S n
  exact @_root_.P2MW.S_IsLocallyConstant_isLocallyConstant_fun_mul_apply_mul_of_hasCompactSupport.solution
