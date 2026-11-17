/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_KaehlerDifferential_exists_unique_smul_D_of_transcendental (git blob 964b3d172f319794fdd552abdd35ff59c68a6011, sha256 02368bdbbd7dc5be888373beeb7da61b497ab09170be054a47833b5280e85ae9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_KaehlerDifferential_span_D_eq_top_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_KaehlerDifferential_D_ne_zero_of_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace KaehlerDifferential
end KaehlerDifferential

namespace P2MW.S_KaehlerDifferential_exists_unique_smul_D_of_transcendental

set_option autoImplicit false

namespace KaehlerDifferential export _root_.KaehlerDifferential (D span_D_eq_top_of_transcendental D_ne_zero_of_transcendental) end KaehlerDifferential
open scoped _root_.KaehlerDifferential in
private theorem KaehlerDifferential.exists_unique_smul_D_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x) [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] (ω : KaehlerDifferential K F) : ∃! c : F, ω = c • KaehlerDifferential.D K F x := by
  have hmem : ω ∈ Submodule.span F ({KaehlerDifferential.D K F x} : Set (KaehlerDifferential K F)) := by
    rw [KaehlerDifferential.span_D_eq_top_of_transcendental K x hx]; exact Submodule.mem_top
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨c, rfl, fun c' hc' => ?_⟩
  have h : (c' - c) • KaehlerDifferential.D K F x = 0 := by rw [sub_smul, ← hc', sub_self]
  rcases smul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (KaehlerDifferential.D_ne_zero_of_transcendental K x hx)

theorem solution (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x) [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] (ω : KaehlerDifferential K F) : ∃! c : F, ω = c • KaehlerDifferential.D K F x :=
  KaehlerDifferential.exists_unique_smul_D_of_transcendental K x hx ω

#print axioms solution
