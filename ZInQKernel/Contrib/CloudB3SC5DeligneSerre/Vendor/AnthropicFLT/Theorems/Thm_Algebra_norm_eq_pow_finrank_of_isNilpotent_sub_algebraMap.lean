/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap (git blob a7a8664fda2060a467dbd84a42c4d5d2cbf12a88, sha256 89b2e67a56d6ac274a6cfbbaea320eb4531b47c1e11e4be3bb90b39522f84fa3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Nilpotent.Defs
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Algebra.norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap {R A : Type*} [CommRing R] [IsDomain R] [Ring A] [Algebra R A] [Module.Free R A] [Module.Finite R A] {a : A} {μ : R} (h : IsNilpotent (a - algebraMap R A μ)) : Algebra.norm R a = μ ^ Module.finrank R A := by
  revert R A a μ h
  exact @_root_.P2MW.S_Algebra_norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap.solution
