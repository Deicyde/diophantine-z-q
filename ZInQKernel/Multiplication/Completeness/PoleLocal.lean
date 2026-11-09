import ZInQKernel.Multiplication.Local.ValHelpers

/-!
# Local behaviour of the products `W = ∏_j (1 + R C_j²)`

Two local facts about a product `W = ∏_j (1 + x_j)` for an additive valuation `v`:

* if every `v(x_j) ≥ m ≥ 1`, then `v(W⁻¹ - 1) ≥ m` (used at the old primes);
* if `v(R) = 1`, then `W⁻¹ ≡ 1` when all `v(C_j) ≥ 0`, and `W⁻¹ ≡ 0` otherwise, modulo
  elements of valuation `≥ 1` (used at a selected prime).
-/

namespace ZInQ.Mult

open scoped BigOperators

variable {K : Type*} [Field K] {v : AddValuation K (WithTop ℤ)}

theorem addVal_prod {ι : Type*} (s : Finset ι) (f : ι → K) :
    v (∏ j ∈ s, f j) = ∑ j ∈ s, v (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, v.map_mul, ih]

/-- If every `v(x_j) ≥ m ≥ 0`, then `v(∏ (1 + x_j) - 1) ≥ m`. -/
theorem vge_prod_one_add_sub_one {ι : Type*} (s : Finset ι) {m : ℤ} (hm : 0 ≤ m) {x : ι → K}
    (hx : ∀ j ∈ s, Vge v m (x j)) : Vge v m (∏ j ∈ s, (1 + x j) - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Vge.zero (v := v) m
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have h1 : Vge v m (x a) := hx a (Finset.mem_insert_self a s)
    have h2 : Vge v m (∏ j ∈ s, (1 + x j) - 1) :=
      ih fun j hj => hx j (Finset.mem_insert_of_mem hj)
    have e : (1 + x a) * ∏ j ∈ s, (1 + x j) - 1 =
        x a + (∏ j ∈ s, (1 + x j) - 1) + x a * (∏ j ∈ s, (1 + x j) - 1) := by ring
    rw [e]
    exact (h1.add h2).add ((h1.mul h2).mono (by linarith))

/-- If `v(w - 1) ≥ m ≥ 1` then `v(w⁻¹ - 1) ≥ m`. -/
theorem vge_inv_sub_one {w : K} {m : ℤ} (hm : 1 ≤ m) (hw : Vge v m (w - 1)) :
    Vge v m (w⁻¹ - 1) := by
  have hw1 : Vge v 1 (w - 1) := hw.mono hm
  have hv : v w = 0 := by
    have := val_one_add hw1
    rwa [add_sub_cancel] at this
  have hw0 : w ≠ 0 := by
    intro h; rw [h, v.map_zero] at hv; exact WithTop.top_ne_coe hv
  have e : w⁻¹ - 1 = -(w - 1) / w := by field_simp; ring
  rw [e]
  exact hw.neg.div_unit hv

/-- **Old primes.** If `v(x_j) ≥ m ≥ 1` for all `j`, then `v((∏_j (1 + x_j))⁻¹ - 1) ≥ m`. -/
theorem vge_inv_prod_sub_one {ι : Type*} (s : Finset ι) {m : ℤ} (hm : 1 ≤ m) {x : ι → K}
    (hx : ∀ j ∈ s, Vge v m (x j)) : Vge v m ((∏ j ∈ s, (1 + x j))⁻¹ - 1) :=
  vge_inv_sub_one hm (vge_prod_one_add_sub_one s (by linarith) hx)

/-- A factor `1 + R C²` with `v(R) = 1` has valuation `≤ 0`, and `≤ -1` when `v(C) < 0`. -/
theorem val_one_add_R_mul_sq {R C : K} (hR : v R = 1) :
    (Vge v 0 C → v (1 + R * C ^ 2) = 0) ∧ (¬ Vge v 0 C → v (1 + R * C ^ 2) ≤ ((-1 : ℤ) : WithTop ℤ)) := by
  constructor
  · intro hC
    apply val_one_add
    have := (Vge.of_eq hR).mul (hC.pow 2)
    exact this.mono (by simp)
  · intro hC
    have hC0 : C ≠ 0 := by rintro rfl; exact hC (Vge.zero 0)
    obtain ⟨n, hn⟩ := val_eq_coe (v := v) hC0
    have hn' : n < 0 := by
      by_contra h; exact hC ((vge_iff_of_eq hn).mpr (by omega))
    have hRC : v (R * C ^ 2) = ((1 + 2 * n : ℤ) : WithTop ℤ) := by
      rw [val_mul_coe hR (val_pow_coe hn 2)]; push_cast; ring_nf
    have : v (R * C ^ 2 + 1) = ((1 + 2 * n : ℤ) : WithTop ℤ) := by
      apply val_add_eq hRC
      rw [Vge, v.map_one]; exact WithTop.coe_le_coe.mpr (by omega) |>.trans (le_of_eq rfl)
    rw [add_comm, this]
    exact WithTop.coe_le_coe.mpr (by omega)

/-- **Selected prime.** If `v(R) = 1` and `W = ∏_j (1 + R C_j²) ≠ 0`, then `W⁻¹ - 1` has
valuation `≥ 1` when all `v(C_j) ≥ 0`, and `W⁻¹` has valuation `≥ 1` otherwise. -/
theorem vge_inv_prod_selected {ι : Type*} (s : Finset ι) {R : K} (hR : v R = 1) {C : ι → K} :
    ((∀ j ∈ s, Vge v 0 (C j)) → Vge v 1 ((∏ j ∈ s, (1 + R * C j ^ 2))⁻¹ - 1)) ∧
      ((∃ j ∈ s, ¬ Vge v 0 (C j)) → Vge v 1 (∏ j ∈ s, (1 + R * C j ^ 2))⁻¹) := by
  constructor
  · intro hC
    refine vge_inv_prod_sub_one s le_rfl fun j hj => ?_
    have := (Vge.of_eq hR).mul ((hC j hj).pow 2)
    exact this.mono (by simp)
  · rintro ⟨j₀, hj₀, hC⟩
    classical
    have hle : ∀ j ∈ s, v (1 + R * C j ^ 2) ≤ 0 := by
      intro j _
      by_cases h : Vge v 0 (C j)
      · exact le_of_eq ((val_one_add_R_mul_sq hR).1 h)
      · exact ((val_one_add_R_mul_sq hR).2 h).trans (WithTop.coe_le_coe.mpr (by omega))
    have hsum : v (∏ j ∈ s, (1 + R * C j ^ 2)) ≤ ((-1 : ℤ) : WithTop ℤ) := by
      rw [addVal_prod, ← Finset.add_sum_erase s _ hj₀]
      have h1 := (val_one_add_R_mul_sq hR).2 hC
      have h2 : ∑ j ∈ s.erase j₀, v (1 + R * C j ^ 2) ≤ 0 :=
        Finset.sum_nonpos fun j hj => hle j (Finset.mem_of_mem_erase hj)
      calc v (1 + R * C j₀ ^ 2) + ∑ j ∈ s.erase j₀, v (1 + R * C j ^ 2)
          ≤ ((-1 : ℤ) : WithTop ℤ) + 0 := add_le_add h1 h2
        _ = ((-1 : ℤ) : WithTop ℤ) := add_zero _
    by_cases hW : ∏ j ∈ s, (1 + R * C j ^ 2) = 0
    · rw [hW, inv_zero]; exact Vge.zero 1
    obtain ⟨n, hn⟩ := val_eq_coe (v := v) hW
    rw [hn] at hsum
    have := WithTop.coe_le_coe.mp hsum
    exact (vge_iff_of_eq (val_inv_coe hn)).mpr (by omega)

end ZInQ.Mult
