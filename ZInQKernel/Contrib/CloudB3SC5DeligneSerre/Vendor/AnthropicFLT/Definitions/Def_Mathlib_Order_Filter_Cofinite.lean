/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_Mathlib_Order_Filter_Cofinite (git blob 3b2f88acf229b7126443bb1d8aa7dec926b6cd0c, sha256 f73b1dea205fc37038a812a37e52f70c32979b98ffa3d87e5744f7dc90ad5641).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

section

lemma Filter.cofinite.sets.countable (ι : Type*) [Countable ι] :
    (Filter.cofinite : Filter ι).sets.Countable :=
  Set.Countable.mono (fun _ h ↦ h) <|
  Set.Countable.preimage_of_injOn Set.Countable.setOf_finite compl_bijective.1.injOn

instance (ι : Type*) [Countable ι] : Countable (.cofinite : Filter ι).sets := by
  rw [Set.countable_coe_iff]
  exact Filter.cofinite.sets.countable ι
