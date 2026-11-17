/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_EisensteinSeries_EisensteinG (git blob 9e0cfc1b00c5a9c0e2f6f6269b94fa131c11f2d2, sha256 196a2302b1409bc64113adb44c98e330710896355845acc155a2fc90a1e7cbcc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace EisensteinSeries

noncomputable def eisensteinG (N : ℕ) (k : ℤ) (a : Fin 2 → ZMod N) (z : UpperHalfPlane) : ℂ :=
  ∑' v : {v : Fin 2 → ℤ // ((↑) : ℤ → ZMod N) ∘ v = a}, eisSummand k v.1 z

end EisensteinSeries
