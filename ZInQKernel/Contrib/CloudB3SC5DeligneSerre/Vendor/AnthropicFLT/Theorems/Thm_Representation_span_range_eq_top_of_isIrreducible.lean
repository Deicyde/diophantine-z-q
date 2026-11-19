/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Representation_span_range_eq_top_of_isIrreducible (git blob eb1d522e081f15534951e174a482e9608e120884, sha256 76ff0055d7f8262f5cd02766472fc979e64bfbc687b2e3f13af40cd00fc0275f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RepresentationTheory.Irreducible
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Representation_span_range_eq_top_of_isIrreducible

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Module LinearMap
theorem Representation.span_range_eq_top_of_isIrreducible
    {k G V : Type*} [Field k] [IsAlgClosed k] [Monoid G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (ρ : Representation k G V) [ρ.IsIrreducible] :
    Submodule.span k (Set.range ⇑ρ) = ⊤ := by
  revert k G V ρ
  exact @_root_.P2MW.S_Representation_span_range_eq_top_of_isIrreducible.solution
