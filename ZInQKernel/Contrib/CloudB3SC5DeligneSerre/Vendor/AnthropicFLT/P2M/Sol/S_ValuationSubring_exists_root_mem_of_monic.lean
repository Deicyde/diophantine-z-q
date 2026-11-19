/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ValuationSubring_exists_root_mem_of_monic (git blob 4e4ee2bb32400fb41099b7f5766bb3dddfff85ad, sha256 9d16e0a46873d0f05265b175bb55eae3407ec683eb2c24fa7290fbbfe269a2d5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Valuation.LocalSubring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ValuationSubring_exists_root_mem_of_monic

set_option autoImplicit false

theorem solution {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) (f : Polynomial A) (hf : f.Monic) (hd : f.natDegree ≠ 0) :
    ∃ x : A, Polynomial.aeval (x : K) f = 0 := by
  have hdeg : (f.map (algebraMap A K)).degree ≠ 0 := by
    rw [hf.degree_map]
    intro h
    exact hd (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr h.le)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap A K)) hdeg
  have hint : IsIntegral A x := by
    refine ⟨f, hf, ?_⟩
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  have hyx : (y : K) = x := hy
  rw [Polynomial.aeval_def, hyx]
  rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx
