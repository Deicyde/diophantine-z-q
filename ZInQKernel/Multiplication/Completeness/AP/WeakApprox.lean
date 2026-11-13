import ZInQKernel.Multiplication.Completeness.WeakApproximation

/-!
# Weak approximation with residue targets

The analogue of `weak_approx_q` used by route AP (`docs/research/nt-22p.md`, §3.2): given
finitely many primes `S` with targets `m_p / p^{k_p}` and exponents `n_p`, finitely many primes
`S'` disjoint from `S`, a real target `x₀`, a radius `δ > 0` and a finite set `X` of excluded
reals, there is a nonzero rational `q` with `|q - m_p/p^{k_p}|_p ≤ p^{-n_p}` on `S`,
`v_p(q) ≥ 0` on `S'`, `|q - x₀| < δ` and `q ∉ X`.

The proof first builds `y = Σ_p (m_p/p^{k_p}) E_p` with Chinese-remainder idempotents
`E_p ≡ 1 (mod p^K)`, `E_p ≡ 0 (mod p'^K)` (`p' ∈ S`, `p' ≠ p`), and then adds the `q'` of
`weak_approx_q` for the target `x₀ - y`.
-/

namespace ZInQ.Mult

open scoped BigOperators

/-- For `q ≠ 0`: `|q|_p ≤ p^{-n}` iff `n ≤ v_p(q)`. -/
theorem padicNorm_le_zpow_iff_ap {p : ℕ} [hp : Fact p.Prime] {q : ℚ} (hq : q ≠ 0) (n : ℤ) :
    padicNorm p q ≤ (p : ℚ) ^ (-n) ↔ n ≤ padicValRat p q := by
  rw [padicNorm.eq_zpow_of_nonzero hq,
    zpow_le_zpow_iff_right₀ (by exact_mod_cast hp.out.one_lt), neg_le_neg_iff]

/-- Chinese-remainder idempotents: `E ≡ 1 (mod p^K)` and `E ≡ 0 (mod p'^K)` for the other
`p' ∈ S`. -/
theorem exists_crt_idempotent_ap (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (K : ℕ) {p : ℕ}
    (hp : p ∈ S) : ∃ E : ℤ, (p : ℤ) ^ K ∣ E - 1 ∧ ∀ p' ∈ S, p' ≠ p → (p' : ℤ) ^ K ∣ E := by
  classical
  have hcop : IsCoprime ((p : ℤ) ^ K) (∏ p' ∈ S.erase p, (p' : ℤ) ^ K) := by
    apply IsCoprime.prod_right
    intro p' hp'
    obtain ⟨hne, hp'S⟩ := Finset.mem_erase.mp hp'
    apply IsCoprime.pow
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_primes (hS p hp) (hS p' hp'S)).mpr hne.symm
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨b * ∏ p' ∈ S.erase p, (p' : ℤ) ^ K, ⟨-a, by linear_combination hab⟩, ?_⟩
  intro p' hp' hne
  exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hne, hp'⟩)) b

/-- `|m / p^k · z|_r ≤ |z|_r` for primes `p ≠ r`. -/
theorem padicNorm_div_pow_mul_le_ap {r p : ℕ} [hr : Fact r.Prime] (hp : p.Prime) (hne : p ≠ r)
    (m : ℤ) (k : ℕ) (z : ℚ) : padicNorm r ((m : ℚ) / (p : ℚ) ^ k * z) ≤ padicNorm r z := by
  have hpk : padicNorm r ((p ^ k : ℕ) : ℚ) = 1 := by
    rw [padicNorm.nat_eq_one_iff]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hr.out hp).mp (hr.out.dvd_of_dvd_pow hd)
    exact hne this.symm
  rw [padicNorm.mul, padicNorm.div, show ((p : ℚ) ^ k) = ((p ^ k : ℕ) : ℚ) by push_cast; rfl,
    hpk, div_one]
  exact mul_le_of_le_one_left (padicNorm.nonneg _) (padicNorm.of_int m)

/-- **Weak approximation with residue targets.** -/
theorem weak_approx_targets (S S' : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (hS' : ∀ p ∈ S', p.Prime)
    (hdisj : Disjoint S S') (m : ℕ → ℤ) (k n : ℕ → ℕ) (x₀ δ : ℝ) (hδ : 0 < δ) (X : Finset ℝ) :
    ∃ q : ℚ, q ≠ 0 ∧ (q : ℝ) ∉ X ∧ |(q : ℝ) - x₀| < δ ∧
      (∀ p ∈ S, padicNorm p (q - m p / (p : ℚ) ^ k p) ≤ (p : ℚ) ^ (-(n p : ℤ))) ∧
      ∀ p ∈ S', 0 ≤ padicValRat p q := by
  classical
  set K : ℕ := ∑ p ∈ S, (n p + k p) with hK
  have hKle : ∀ p ∈ S, n p + k p ≤ K := fun p hp =>
    Finset.single_le_sum (f := fun p => n p + k p) (fun _ _ => Nat.zero_le _) hp
  choose! E hE1 hE0 using fun p (hp : p ∈ S) => exists_crt_idempotent_ap S hS K hp
  set y : ℚ := ∑ p ∈ S, ((m p : ℚ) / (p : ℚ) ^ k p) * E p with hy
  -- `y` is close to the targets
  have hy_near : ∀ p ∈ S, padicNorm p (y - m p / (p : ℚ) ^ k p) ≤ (p : ℚ) ^ (-(n p : ℤ)) := by
    intro p hp
    have : Fact p.Prime := ⟨hS p hp⟩
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast (hS p hp).ne_zero
    rw [hy, ← Finset.add_sum_erase S _ hp]
    obtain ⟨a, ha⟩ := hE1 p hp
    have hkK : k p ≤ K := le_trans (Nat.le_add_left _ _) (hKle p hp)
    have h1 : (m p : ℚ) / (p : ℚ) ^ k p * E p - m p / (p : ℚ) ^ k p =
        ((m p * a * (p : ℤ) ^ (K - k p) : ℤ) : ℚ) := by
      have hE : (E p : ℚ) = 1 + (p : ℚ) ^ K * a := by
        have := congrArg (fun z : ℤ => (z : ℚ)) ha
        push_cast at this; linarith
      rw [hE]
      have hpow : (p : ℚ) ^ K = (p : ℚ) ^ (K - k p) * (p : ℚ) ^ k p := by
        rw [← pow_add, Nat.sub_add_cancel hkK]
      rw [hpow]
      push_cast
      field_simp
      ring
    have h2 : padicNorm p ((m p * a * (p : ℤ) ^ (K - k p) : ℤ) : ℚ) ≤ (p : ℚ) ^ (-(n p : ℤ)) := by
      have hd : ((p ^ n p : ℕ) : ℤ) ∣ m p * a * (p : ℤ) ^ (K - k p) := by
        push_cast
        exact Dvd.dvd.mul_left (pow_dvd_pow _ (by have := hKle p hp; omega)) _
      exact_mod_cast (padicNorm.dvd_iff_norm_le).mp hd
    have h3 : padicNorm p (∑ p' ∈ S.erase p, (m p' : ℚ) / (p' : ℚ) ^ k p' * E p') ≤
        (p : ℚ) ^ (-(n p : ℤ)) := by
      refine padicNorm.sum_le' (fun p' hp' => ?_) (by positivity)
      obtain ⟨hne, hp'S⟩ := Finset.mem_erase.mp hp'
      refine (padicNorm_div_pow_mul_le_ap (hS p' hp'S) hne _ _ _).trans ?_
      have hd : ((p ^ n p : ℕ) : ℤ) ∣ E p' := by
        push_cast
        exact (pow_dvd_pow _ (le_trans (Nat.le_add_right _ _) (hKle p hp))).trans
          (hE0 p' hp'S p hp hne.symm)
      exact_mod_cast (padicNorm.dvd_iff_norm_le).mp hd
    have : (m p : ℚ) / (p : ℚ) ^ k p * E p +
        ∑ p' ∈ S.erase p, (m p' : ℚ) / (p' : ℚ) ^ k p' * E p' - m p / (p : ℚ) ^ k p =
        ((m p * a * (p : ℤ) ^ (K - k p) : ℤ) : ℚ) +
          ∑ p' ∈ S.erase p, (m p' : ℚ) / (p' : ℚ) ^ k p' * E p' := by
      rw [← h1]; ring
    rw [this]
    exact (padicNorm.nonarchimedean).trans (max_le h2 h3)
  -- `y` is integral at `S'`
  have hy_int : ∀ p ∈ S', padicNorm p y ≤ 1 := by
    intro p hp
    have : Fact p.Prime := ⟨hS' p hp⟩
    refine padicNorm.sum_le' (fun p' hp' => ?_) zero_le_one
    have hne : p' ≠ p := fun h => Finset.disjoint_left.mp hdisj hp' (h ▸ hp)
    exact (padicNorm_div_pow_mul_le_ap (hS p' hp') hne _ _ _).trans (padicNorm.of_int _)
  obtain ⟨q', hq'0, hq'X, hq'δ, hq'S, hq'S'⟩ := weak_approx_q S S' hS hS' n (x₀ - y) δ hδ
    ((insert (0 : ℝ) X).image (fun r => r - (y : ℝ)))
  have hnot : ∀ r ∈ insert (0 : ℝ) X, ((y + q' : ℚ) : ℝ) ≠ r := by
    intro r hr h
    apply hq'X
    refine Finset.mem_image.mpr ⟨r, hr, ?_⟩
    rw [← h]; push_cast; ring
  refine ⟨y + q', ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hnot 0 (Finset.mem_insert_self _ _) (by rw [h]; simp)
  · exact fun h => hnot _ (Finset.mem_insert_of_mem h) rfl
  · push_cast
    have : (y : ℝ) + q' - x₀ = q' - (x₀ - y) := by ring
    rw [this]; exact hq'δ
  · intro p hp
    have : Fact p.Prime := ⟨hS p hp⟩
    have hq' : padicNorm p q' ≤ (p : ℚ) ^ (-(n p : ℤ)) :=
      (padicNorm_le_zpow_iff_ap hq'0 _).mpr (hq'S p hp)
    have : y + q' - m p / (p : ℚ) ^ k p = (y - m p / (p : ℚ) ^ k p) + q' := by ring
    rw [this]
    exact (padicNorm.nonarchimedean).trans (max_le (hy_near p hp) hq')
  · intro p hp
    have : Fact p.Prime := ⟨hS' p hp⟩
    have hq0 : y + q' ≠ 0 := fun h => hnot 0 (Finset.mem_insert_self _ _) (by rw [h]; simp)
    have hq' : padicNorm p q' ≤ 1 := by
      have := (padicNorm_le_zpow_iff_ap hq'0 0).mpr (hq'S' p hp)
      simpa using this
    have h := (padicNorm.nonarchimedean (p := p) (q := y) (r := q')).trans
      (max_le (hy_int p hp) hq')
    have := (padicNorm_le_zpow_iff_ap hq0 0).mp (by simpa using h)
    exact this

end ZInQ.Mult
