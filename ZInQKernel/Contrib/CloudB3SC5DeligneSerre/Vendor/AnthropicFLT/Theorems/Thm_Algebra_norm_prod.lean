/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_norm_prod (git blob 473b03f62ade63356f6bc2d0125393fd618b07c9, sha256 fafe886332dbca0f7df517e98e07d43f6e28d314e96bfe35389233ab228d3157).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.Norm.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_norm_prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Algebra.norm_prod {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A] [Algebra R B] [Module.Free R A] [Module.Finite R A] [Module.Free R B] [Module.Finite R B] (x : A × B) : Algebra.norm R x = Algebra.norm R x.1 * Algebra.norm R x.2 := by
  revert R A B x
  exact @_root_.P2MW.S_Algebra_norm_prod.solution
