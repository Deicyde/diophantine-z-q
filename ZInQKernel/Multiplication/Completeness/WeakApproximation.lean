import Mathlib

/-!
# Weak approximation for the parameter `q`

Given finitely many primes `S` with exponents `e_p`, finitely many primes `S'`, a real target
`x₀`, a radius `δ > 0` and a finite set `X` of excluded reals, there is a nonzero rational `q`
with `v_p(q) ≥ e_p` on `S`, `v_p(q) ≥ 0` on `S'`, `|q - x₀| < δ` and `q ∉ X`. The proof takes
`q = m / ℓ^k` with `M = ∏_{p ∈ S} p^{e_p}` dividing `m` and `ℓ` a prime outside `S ∪ S'`.
-/

namespace ZInQ.Mult

open scoped BigOperators

/-- The valuation of `m / ℓ^k` at a prime `p ≠ ℓ` is that of the integer `m`. -/
theorem padicValRat_div_prime_pow {p ℓ : ℕ} [Fact p.Prime] (hℓ : ℓ.Prime) (hpℓ : p ≠ ℓ)
    {m : ℤ} (hm : m ≠ 0) (k : ℕ) :
    padicValRat p ((m : ℚ) / (ℓ : ℚ) ^ k) = padicValInt p m := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ0 : ((ℓ : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hℓ.ne_zero)
  rw [padicValRat.div (by exact_mod_cast hm) hℓ0, padicValRat.of_int, padicValRat.pow,
    padicValRat.of_nat, padicValNat_primes hpℓ]
  simp

/-- **Weak approximation for the parameter `q`.** The manuscript's statement also assumes `S`
and `S'` disjoint; this is not needed. Since `padicValRat p 0 = 0`, the conclusion includes
`q ≠ 0`. -/
theorem weak_approx_q (S S' : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hS' : ∀ p ∈ S', p.Prime)
    (e : ℕ → ℕ) (x₀ δ : ℝ) (hδ : 0 < δ) (X : Finset ℝ) :
    ∃ q : ℚ, q ≠ 0 ∧ (q : ℝ) ∉ X ∧ |(q : ℝ) - x₀| < δ ∧
      (∀ p ∈ S, (e p : ℤ) ≤ padicValRat p q) ∧ ∀ p ∈ S', 0 ≤ padicValRat p q := by
  classical
  -- a prime `ℓ` outside `S ∪ S'`
  obtain ⟨ℓ, hℓbig, hℓ⟩ := Nat.exists_infinite_primes ((S ∪ S').sup id + 1)
  have hℓS : ∀ p ∈ S ∪ S', p ≠ ℓ := by
    intro p hp hpℓ
    have : p ≤ (S ∪ S').sup id := Finset.le_sup (f := id) hp
    omega
  set M : ℕ := ∏ p ∈ S, p ^ e p with hMdef
  have hMpos : 0 < M := Finset.prod_pos fun p hp => pow_pos (hS p hp).pos _
  -- the grid spacing `g = M / ℓ^k` is below `δ / N`
  set N : ℕ := (insert (0 : ℝ) X).card + 1 with hN
  have hℓ1 : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((M : ℝ) * N / δ) hℓ1
  set g : ℝ := (M : ℝ) / (ℓ : ℝ) ^ k with hg
  have hℓk : (0 : ℝ) < (ℓ : ℝ) ^ k := pow_pos (by linarith) _
  have hgpos : 0 < g := div_pos (by exact_mod_cast hMpos) hℓk
  have hNpos : (0 : ℝ) < N := by positivity
  have hgN : g * N < δ := by
    rw [hg, div_mul_eq_mul_div, div_lt_iff₀ hℓk]
    rw [div_lt_iff₀ hδ] at hk
    linarith
  set n₀ : ℤ := ⌊x₀ / g⌋ with hn₀
  -- the candidates `(n₀ + i + 1) g`, `i < N`
  let cand : ℕ → ℚ := fun i => ((n₀ + i + 1 : ℤ) * M : ℤ) / (ℓ : ℚ) ^ k
  have hcand_real : ∀ i, ((cand i : ℚ) : ℝ) = ((n₀ + i + 1 : ℤ) : ℝ) * g := by
    intro i
    simp only [cand, hg]
    push_cast
    ring
  have hcand_inj : Function.Injective cand := by
    intro i j hij
    have h := congrArg (fun q : ℚ => (q : ℝ)) hij
    simp only [hcand_real] at h
    have h2 := mul_right_cancel₀ hgpos.ne' h
    have h3 : ((n₀ + i + 1 : ℤ)) = ((n₀ + j + 1 : ℤ)) := by exact_mod_cast h2
    omega
  set T : Finset ℝ := (Finset.range N).image fun i => ((cand i : ℚ) : ℝ) with hT
  have hTcard : T.card = N := by
    rw [hT, Finset.card_image_of_injective _ (f := fun i => ((cand i : ℚ) : ℝ))
      ((Rat.cast_injective).comp hcand_inj), Finset.card_range]
  obtain ⟨y, hyT, hyX⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := insert (0 : ℝ) X) (t := T) (by rw [hTcard, hN]; omega)
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hyT
  rw [Finset.mem_insert, not_or] at hyX
  have hi' : (i : ℝ) + 1 ≤ N := by
    have := Finset.mem_range.mp hi
    exact_mod_cast this
  refine ⟨cand i, fun h => hyX.1 (by rw [h]; simp), hyX.2, ?_, ?_, ?_⟩
  · -- closeness
    rw [hcand_real]
    have h1 : (n₀ : ℝ) ≤ x₀ / g := Int.floor_le _
    have h2 : x₀ / g < n₀ + 1 := Int.lt_floor_add_one _
    have h1' : (n₀ : ℝ) * g ≤ x₀ := by rwa [le_div_iff₀ hgpos] at h1
    have h2' : x₀ < ((n₀ : ℝ) + 1) * g := by rwa [div_lt_iff₀ hgpos] at h2
    rw [abs_lt]
    push_cast
    constructor <;> nlinarith
  all_goals
    have hq0 : cand i ≠ 0 := fun h => hyX.1 (by rw [h]; simp)
    have hm0 : ((n₀ + i + 1 : ℤ) * M : ℤ) ≠ 0 := by
      intro h; apply hq0; simp only [cand]; rw [h]; simp
  · intro p hp
    have : Fact p.Prime := ⟨hS p hp⟩
    simp only [cand]
    rw [padicValRat_div_prime_pow hℓ (hℓS p (Finset.mem_union_left _ hp)) hm0]
    have hdvd : ((p ^ e p : ℕ) : ℤ) ∣ (n₀ + i + 1 : ℤ) * M :=
      Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr (Finset.dvd_prod_of_mem _ hp)) _
    push_cast at hdvd
    have := (padicValInt_dvd_iff (p := p) (e p) _).mp hdvd
    rcases this with h | h
    · exact absurd h hm0
    · exact_mod_cast h
  · intro p hp
    have : Fact p.Prime := ⟨hS' p hp⟩
    simp only [cand]
    rw [padicValRat_div_prime_pow hℓ (hℓS p (Finset.mem_union_right _ hp)) hm0]
    exact Int.natCast_nonneg _

end ZInQ.Mult
