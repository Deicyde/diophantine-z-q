import ZInQKernel.Compiler.Circuits.Packed.Masks

/-!
# One active state per time slot

Let `m < B` and let `S_0, …, S_{m-1}` have zero-one base-`B` digits `σ_i(t)` (`t ≤ q`). Then
`S_0 + ⋯ + S_{m-1} = F_q` and `S_{m-1} = B^q` hold iff in every slot `t ≤ q` exactly one state
digit is `1` and the last state's digit is `1` exactly at `t = q`.

(Blueprint: `compiler/natural/packed/packed-state-selection.md`.)
-/

namespace ZInQ.Compiler.Packed

open Finset

theorem pack_indicator_top (B q : ℕ) : pack B (fun t => if t = q then 1 else 0) q = B ^ q := by
  rcases q with _ | q
  · simp
  · rw [pack_succ_top, ite_eq_left rfl, one_mul,
      pack_congr (g := fun _ => 0) fun t ht => ite_eq_right (by omega), pack_const_zero, zero_add]

/-- A sum of zero-one values is `1` iff exactly one of them is `1`. -/
theorem sum_range_eq_one_iff {m : ℕ} {f : ℕ → ℕ} (hf : ∀ i < m, f i ≤ 1) :
    ∑ i ∈ range m, f i = 1 ↔ ∃! i, i < m ∧ f i = 1 := by
  constructor
  · intro h
    have hex : ∃ i ∈ range m, f i ≠ 0 := by
      by_contra hne
      push Not at hne
      rw [Finset.sum_eq_zero hne] at h
      exact zero_ne_one h
    obtain ⟨i, hi, hfi⟩ := hex
    have hi' := Finset.mem_range.1 hi
    have hfi1 : f i = 1 := by have := hf i hi'; omega
    refine ⟨i, ⟨hi', hfi1⟩, fun j ⟨hj, hfj⟩ => ?_⟩
    by_contra hji
    have : f i + f j ≤ ∑ k ∈ range m, f k := by
      rw [← Finset.sum_pair (Ne.symm hji)]
      exact Finset.sum_le_sum_of_subset (by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl <;> simpa)
    omega
  · rintro ⟨i, ⟨hi, hfi⟩, huniq⟩
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.2 hi) fun j hj hji => by
      have := hf j (Finset.mem_range.1 hj)
      by_contra hne
      exact hji (huniq j ⟨Finset.mem_range.1 hj, by omega⟩)]
    exact hfi

/-- **One active state per time slot.** -/
theorem one_active_state {B q m : ℕ} (hm : m < B) (hm0 : 0 < m) (σ : ℕ → ℕ → ℕ)
    (hσ : ∀ i < m, ∀ t ≤ q, σ i t ≤ 1) :
    (∑ i ∈ range m, ∑ t ∈ range (q + 1), σ i t * B ^ t = ∑ t ∈ range (q + 1), B ^ t ∧
      ∑ t ∈ range (q + 1), σ (m - 1) t * B ^ t = B ^ q) ↔
    (∀ t ≤ q, ∃! i, i < m ∧ σ i t = 1) ∧ (∀ t ≤ q, σ (m - 1) t = 1 ↔ t = q) := by
  have hsum : ∑ i ∈ range m, ∑ t ∈ range (q + 1), σ i t * B ^ t =
      pack B (fun t => ∑ i ∈ range m, σ i t) q := by
    rw [← pack_sum]; rfl
  have hF : ∑ t ∈ range (q + 1), B ^ t = pack B (fun _ => 1) q := by simp [pack]
  have hdig : ∀ t ≤ q, ∑ i ∈ range m, σ i t < B := fun t ht =>
    lt_of_le_of_lt ((Finset.sum_le_sum fun i hi => hσ i (Finset.mem_range.1 hi) t ht).trans
      (by simp)) hm
  rw [hsum, hF, ← pack_def, ← pack_indicator_top B q]
  have hB : 1 < B := by omega
  constructor
  · rintro ⟨h1, h2⟩
    have e1 := pack_inj hdig (fun _ _ => hB) h1
    have e2 := pack_inj (fun t ht => lt_of_le_of_lt (hσ (m - 1) (by omega) t ht) hB)
      (fun t _ => by split_ifs <;> omega) h2
    refine ⟨fun t ht => (sum_range_eq_one_iff fun i hi => hσ i hi t ht).1 (e1 t ht),
      fun t ht => ?_⟩
    rw [e2 t ht]
    split_ifs <;> simp_all
  · rintro ⟨h1, h2⟩
    refine ⟨pack_congr fun t ht => (sum_range_eq_one_iff fun i hi => hσ i hi t ht).2 (h1 t ht),
      pack_congr fun t ht => ?_⟩
    have := hσ (m - 1) (by omega) t ht
    split_ifs with htq
    · exact (h2 t ht).2 htq
    · have : σ (m - 1) t ≠ 1 := fun h => htq ((h2 t ht).1 h)
      omega

end ZInQ.Compiler.Packed
