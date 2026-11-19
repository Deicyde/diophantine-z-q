/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_le_dedekindPsi (git blob 1c0e01b02581e4b785eebbdb52643335cb09a634, sha256 466e0b19041f71675359c7e38a5674d3301ed90db646ecc7b191160cce1f8ddf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Squarefree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_le_dedekindPsi

open ModularCurve Finset

theorem solution (N : ℕ) (hN : N ≠ 0) : N ≤ dedekindPsi N := by
  rw [dedekindPsi]
  have h1 : (1 : ℕ) ∈ {d ∈ N.divisors | Squarefree d} :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hN, squarefree_one⟩
  simpa using Finset.single_le_sum (f := fun d => N / d) (fun d _ => Nat.zero_le _) h1
