/-
rv-jac-ext: the glue pieces of the degree-one-divisor extension that can be stated over Mathlib
today (no curves, no Jacobians).  Mathlib only; nothing imports the project.

1. `perm_eq_one_of_fixes_pairs`: a permutation of a set with at least three elements that fixes
   every two-element subset is the identity.  (Applied to the six Weierstrass points `W₁..W₆` of a
   genus-2 curve: `σ ∈ G_K` fixing `J[2]` pointwise fixes each class `[W_i − W_j]`; these 15
   classes are distinct, so `σ` fixes every pair `{W_i, W_j}`, hence every `W_i`.)
2. `finrank_finset_sup_le`: a compositum of `n` intermediate fields, each of degree `≤ c`, has
   degree `≤ c ^ n`.
3. The degree arithmetic of route W′ (`[K̃:ℚ] ≤ k·12^k ≤ 324! = F₀` for `k ≤ 324`) and of
   route L (`12·[L:ℚ] ≤ D` when `[L:ℚ] ≤ k·3^{(16k²)²}`, `k ≤ 324`).
-/
import Mathlib

set_option exponentiation.threshold 400

namespace RvJacExt

open Module

/-! ### 1. Permutations fixing all pairs -/

theorem perm_eq_one_of_fixes_pairs {α : Type*} [DecidableEq α] [Fintype α]
    (h3 : 3 ≤ Fintype.card α) (σ : Equiv.Perm α)
    (h : ∀ i j : α, i ≠ j → ({σ i, σ j} : Finset α) = {i, j}) : σ = 1 := by
  ext i
  simp only [Equiv.Perm.coe_one, id_eq]
  -- choose `j, k` distinct from `i` and from each other
  have hcard : 2 ≤ (Finset.univ.erase i).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]; omega
  obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp (by omega : 1 < (Finset.univ.erase i).card)
  have hij : i ≠ j := fun e => (Finset.mem_erase.mp hj).1 e.symm
  have hik : i ≠ k := fun e => (Finset.mem_erase.mp hk).1 e.symm
  have h1 : σ i ∈ ({i, j} : Finset α) := by rw [← h i j hij]; simp
  have h2 : σ i ∈ ({i, k} : Finset α) := by rw [← h i k hik]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
  rcases h1 with h1 | h1
  · exact h1
  · rcases h2 with h2 | h2
    · exact h2
    · exact absurd (h1.symm.trans h2) hjk

/-! ### 2. Degree of a compositum -/

theorem finrank_finset_sup_le {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {ι : Type*} [DecidableEq ι] (t : ι → IntermediateField K Ω) (c : ℕ)
    (ht : ∀ i, finrank K (t i) ≤ c) (s : Finset ι) :
    finrank K ↥(s.sup t : IntermediateField K Ω) ≤ c ^ s.card := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sup_empty, IntermediateField.finrank_bot]; simp
  | insert a s ha ih =>
    rw [Finset.sup_insert, Finset.card_insert_of_notMem ha, pow_succ]
    have h := IntermediateField.finrank_sup_le (t a) (s.sup t)
    calc _ ≤ _ := h
      _ ≤ c * c ^ s.card := Nat.mul_le_mul (ht a) ih
      _ = c ^ s.card * c := Nat.mul_comm _ _

/-! ### 3. Degree arithmetic -/

/-- `F₀ = 324!` (as in `ZInQKernel/Hypotheses/Height.lean`, `heightF0`). -/
irreducible_def F0 : ℕ := Nat.factorial 324

/-- `D = F₀ · 3^(256 F₀⁴)` (as in `Height.lean`). -/
def Dconst : ℕ := F0 * 3 ^ (256 * F0 ^ 4)

theorem twelve_pow_bound : 324 * 12 ^ 324 ≤ F0 := by
  rw [F0_def]; decide +kernel

/-- Route W′: if `[K:ℚ] = k ≤ 324` and `[K̃:K] ≤ 12^k`, then `[K̃:ℚ] ≤ F₀`. -/
theorem routeW_degree (k m : ℕ) (hk : k ≤ 324) (hm : m ≤ 12 ^ k) : k * m ≤ F0 := by
  calc k * m ≤ 324 * 12 ^ 324 :=
        Nat.mul_le_mul hk (hm.trans (Nat.pow_le_pow_right (by norm_num) hk))
    _ ≤ F0 := twelve_pow_bound

/-- Route W′ in field form: tower law plus the bound. -/
theorem routeW_finrank {K M : Type*} [Field K] [Field M] [CharZero K] [CharZero M]
    [Algebra K M] [Algebra ℚ K] [Algebra ℚ M] [IsScalarTower ℚ K M]
    [FiniteDimensional ℚ K] [FiniteDimensional K M]
    (hk : finrank ℚ K ≤ 324) (hm : finrank K M ≤ 12 ^ finrank ℚ K) :
    finrank ℚ M ≤ F0 := by
  rw [← Module.finrank_mul_finrank ℚ K M]
  exact routeW_degree _ _ hk hm

theorem twelve_mul_le_F0 : 12 * 324 ≤ F0 := by rw [F0_def]; decide +kernel

/-- Route L: if `[L:ℚ] ≤ k·3^{(16k²)²}` with `1 ≤ k ≤ 324` (A8's bound with `[K:ℚ] = k`), then
`12·[L:ℚ] ≤ D`. -/
theorem routeL_degree (k d : ℕ) (hk : k ≤ 324) (hd : d ≤ k * 3 ^ ((16 * k ^ 2) ^ 2)) :
    12 * d ≤ Dconst := by
  unfold Dconst
  have hF : 324 ≤ F0 := le_trans (by norm_num) twelve_mul_le_F0
  have e1 : (16 * k ^ 2) ^ 2 ≤ 256 * F0 ^ 4 := by
    have : k ≤ F0 := hk.trans hF
    have h4 : k ^ 4 ≤ F0 ^ 4 := Nat.pow_le_pow_left this 4
    calc (16 * k ^ 2) ^ 2 = 256 * k ^ 4 := by ring
      _ ≤ 256 * F0 ^ 4 := Nat.mul_le_mul_left _ h4
  calc 12 * d ≤ 12 * (k * 3 ^ ((16 * k ^ 2) ^ 2)) := Nat.mul_le_mul_left _ hd
    _ = (12 * k) * 3 ^ ((16 * k ^ 2) ^ 2) := by ring
    _ ≤ F0 * 3 ^ (256 * F0 ^ 4) :=
        Nat.mul_le_mul ((Nat.mul_le_mul_left 12 hk).trans twelve_mul_le_F0)
          (Nat.pow_le_pow_right (by norm_num) e1)

/-- Route L with A10's rank `r = 4k²` instead of Mumford's `16k²`: works for every `k ≤ F₀`,
so it needs no refinement of N5's `[K:ℚ] ≤ 324!`. -/
theorem routeL_degree_noCM (k d : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ F0)
    (hd : d ≤ k * 3 ^ ((4 * k ^ 2) ^ 2)) : 12 * d ≤ Dconst := by
  unfold Dconst
  have h4 : k ^ 4 ≤ F0 ^ 4 := Nat.pow_le_pow_left hk 4
  have hpos : 1 ≤ k ^ 4 := Nat.one_le_pow _ _ hk1
  have e : 16 * k ^ 4 + 3 ≤ 256 * F0 ^ 4 := by omega
  calc 12 * d ≤ 12 * (k * 3 ^ ((4 * k ^ 2) ^ 2)) := Nat.mul_le_mul_left _ hd
    _ ≤ 27 * (k * 3 ^ (16 * k ^ 4)) := by
        rw [show (4 * k ^ 2) ^ 2 = 16 * k ^ 4 by ring]
        exact Nat.mul_le_mul_right _ (by norm_num)
    _ = k * 3 ^ (16 * k ^ 4 + 3) := by ring
    _ ≤ F0 * 3 ^ (256 * F0 ^ 4) := Nat.mul_le_mul hk (Nat.pow_le_pow_right (by norm_num) e)

end RvJacExt

#print axioms RvJacExt.perm_eq_one_of_fixes_pairs
#print axioms RvJacExt.finrank_finset_sup_le
#print axioms RvJacExt.routeW_finrank
#print axioms RvJacExt.routeL_degree
#print axioms RvJacExt.routeL_degree_noCM
