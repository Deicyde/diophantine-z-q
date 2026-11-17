/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PeriodPair_sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq (git blob 298aec965e896169eef6b6090bf9b259b4659d1f, sha256 fdb542a081ae6bca6af6ed9cd07708fe4e6184354cbb386236344b6f4c5632ab).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_PeriodPair_sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem PeriodPair.sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq (L : PeriodPair) {a b : ℂ}
    (ha : a ∉ L.lattice) (hb : b ∉ L.lattice) (h : L.weierstrassP a = L.weierstrassP b) :
    a - b ∈ L.lattice ∨ a + b ∈ L.lattice := by
  revert L a b ha hb h
  exact @_root_.P2MW.S_PeriodPair_sub_mem_lattice_or_add_mem_lattice_of_weierstrassP_eq.solution
