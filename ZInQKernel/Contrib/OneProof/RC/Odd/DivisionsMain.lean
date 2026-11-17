import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Odd.Divisions

/-!
# Lane RC12-odd: (O.9), (O.11), the fresh reading and the omission coefficient

Manuscript (11/5), Appendix F, proof of Proposition `ex:app-coefficient-rules`
(tex 9558–9636, 9681–9687, 9905–9918). See `Divisions.lean` for the setting. All PROVED.
-/

namespace ZInQ.Manuscript.RC.Odd

variable {R : Type*} [CommRing R]

theorem two_pow_dvd_intCast_four_mul {k : ℕ} {x : R} {c : ℤ} (hc : (4 : ℤ) ∣ c)
    (h : (2 : R) ^ k ∣ x) : (2 : R) ^ (k + 2) ∣ (c : R) * x := by
  obtain ⟨d, rfl⟩ := hc
  have : ((4 * d : ℤ) : R) * x = (d : R) * (2 ^ 2 * x) := by push_cast; ring
  rw [this, pow_add, mul_comm ((2 : R) ^ k)]
  exact dvd_mul_of_dvd_right (mul_dvd_mul_left _ h) _

theorem legendreSym_neg_eq_one_or {p : ℕ} [Fact p.Prime] {n : ℕ} (hpn : ¬ p ∣ n) {ε : ℤ}
    (hε : ε = 1 ∨ ε = -1) : ε * legendreSym p (-(n : ℤ)) = 1 ∨ ε * legendreSym p (-(n : ℤ)) = -1 := by
  have h0 : ((-(n : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    intro h; apply hpn
    have : (p : ℤ) ∣ -(n : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h
    exact Int.natCast_dvd_natCast.mp (dvd_neg.mp this)
  rcases legendreSym.eq_one_or_neg_one p h0 with h | h <;> rcases hε with rfl | rfl <;>
    simp [h]

/-- The hypotheses on the coefficient source (see the module docstring of `Divisions.lean`). -/
structure SourceHyp (T δ : ℕ) (χ : ℕ → R) (GoodPrime : ℕ → Prop) (ap : ℕ → ℤ) (a : ℕ → R) :
    Prop where
  prime : ∀ q, GoodPrime q → q.Prime
  odd : ∀ q, GoodPrime q → Odd (q : ℤ)
  ap_mod : ∀ q, GoodPrime q → ap q ≡ q + 1 [ZMOD 4]
  rec : ∀ q (hq : GoodPrime q), ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
    @RecAt R _ q ⟨prime q hq⟩ (χ q) ε (ap q) a
  zero : a 0 = 0
  depth : ∀ n, (2 : R) ^ (min T (δ + (oddPart n).card)) ∣ a n
  mul : ∀ x y, χ (x * y) = χ x * χ y
  one : χ 1 = 1

theorem SourceHyp.pow {T δ : ℕ} {χ : ℕ → R} {G : ℕ → Prop} {ap : ℕ → ℤ} {a : ℕ → R}
    (H : SourceHyp T δ χ G ap a) (q t : ℕ) : χ (q ^ t) = χ q ^ t := by
  induction t with
  | zero => simp [H.one]
  | succ t ih => rw [pow_succ, H.mul, ih, pow_succ]

/-- **PROVED (the inductive step behind (O.9) and (O.11), tex 9567–9617).** -/
theorem DivInv.step {T δ : ℕ} {χ : ℕ → R} {GoodPrime : ℕ → Prop} {U : Finset ℕ} {b : ℕ → R}
    (h : DivInv T δ χ GoodPrime U b) {p : ℕ} [hp : Fact p.Prime] (hpU : p ∉ U)
    (hpodd : Odd (p : ℤ)) {ε ap : ℤ} (hε : ε = 1 ∨ ε = -1) (hap : ap ≡ p + 1 [ZMOD 4])
    (hrec : RecAt p (χ p) ε ap b) (hχ : ∀ x y, χ (x * y) = χ x * χ y) (hχ1 : χ 1 = 1) :
    DivInv T δ χ GoodPrime (insert p U) (Top p (χ p) b) := by
  have hp0 : 0 < p := hp.out.pos
  have hcard : (insert p U).card = U.card + 1 := Finset.card_insert_of_notMem hpU
  have hχpow : ∀ t, χ (p ^ t) = χ p ^ t := by
    intro t; induction t with
    | zero => simp [hχ1]
    | succ t ih => rw [pow_succ, hχ, ih, pow_succ]
  have hzero : Top p (χ p) b 0 = 0 := by simp [Top, divCoeff, h.zero]
  refine ⟨hzero, ?_, ?_⟩
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hzero]; exact dvd_zero _
    obtain ⟨k, n', hpn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.ne_one
    have hn' : n' ≠ 0 := by rintro rfl; simp at hn
    have hnp := not_mem_oddPart_of_not_dvd hpn'
    obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [Top_even hrec hpn' s, oddPart_pow_even_mul hp.out hn' hpn',
        Finset.sdiff_insert_of_notMem hnp, hcard]
      have hb := h.bound (p * n')
      rw [oddPart_mul_prime hp.out hn' hpn', Finset.insert_sdiff_of_notMem _ hpU,
        Finset.card_insert_of_notMem (fun h' => hnp (Finset.mem_sdiff.mp h').1)] at hb
      apply dvd_mul_of_dvd_right
      convert hb using 3; ring
    · rw [Top_odd hrec hpn' s, oddPart_pow_odd_mul hp.out hn' hpn', Finset.insert_sdiff_insert,
        Finset.sdiff_insert_of_notMem hnp, hcard]
      have hb := h.bound n'
      have hκ := legendreSym_neg_eq_one_or hpn' hε
      have hev := (shellDiff_modEq hκ hpodd hap s).2
      rw [mul_assoc]
      apply dvd_mul_of_dvd_right
      exact two_pow_dvd_of_le (by omega) (two_pow_dvd_intCast_even_mul hev hb)
  · intro n m hn hm hgood hcop
    obtain ⟨k, n', hpn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.out.ne_one
    obtain ⟨t, m₀, hpm₀, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.out.ne_one
    have hn' : n' ≠ 0 := by rintro rfl; simp at hn
    have hm₀ : m₀ ≠ 0 := by rintro rfl; simp at hm
    have hnp := not_mem_oddPart_of_not_dvd hpn'
    have hpn'' : ¬ p ∣ n' * m₀ ^ 2 := by
      intro hd
      rcases (Nat.Prime.dvd_mul hp.out).mp hd with h1 | h1
      · exact hpn' h1
      · exact hpm₀ (hp.out.dvd_of_dvd_pow h1)
    have hgood₀ : ∀ q ∈ m₀.primeFactors, GoodPrime q := by
      intro q hq
      apply hgood q
      rw [Nat.primeFactors_mul (pow_ne_zero _ hp.out.ne_zero) hm₀]
      exact Finset.mem_union_right _ hq
    have hχm : χ (p ^ t * m₀) = χ p ^ t * χ m₀ := by rw [hχ, hχpow]
    have hcop' : ∀ q ∈ oddPart n' \ U, ¬ q ∣ m₀ := by
      intro q hq hqm
      have hqp : q ≠ p := fun e => hnp (e ▸ (Finset.mem_sdiff.mp hq).1)
      obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' k
      · apply hcop q _ (dvd_mul_of_dvd_right hqm _)
        rw [oddPart_pow_even_mul hp.out hn' hpn', Finset.mem_sdiff, Finset.mem_insert]
        exact ⟨(Finset.mem_sdiff.mp hq).1, by rintro (e | e); exact hqp e;
          exact (Finset.mem_sdiff.mp hq).2 e⟩
      · apply hcop q _ (dvd_mul_of_dvd_right hqm _)
        rw [oddPart_pow_odd_mul hp.out hn' hpn', Finset.mem_sdiff, Finset.mem_insert,
          Finset.mem_insert]
        exact ⟨Or.inr (Finset.mem_sdiff.mp hq).1, by rintro (e | e); exact hqp e;
          exact (Finset.mem_sdiff.mp hq).2 e⟩
    obtain ⟨s, rfl | rfl⟩ := Nat.even_or_odd' k
    · -- `p ∉ J`: odd factors `b⁰_s − b⁰_{s−1}`
      rw [oddPart_pow_even_mul hp.out hn' hpn', Finset.sdiff_insert_of_notMem hnp, hcard]
      have hidx : p ^ (2 * s) * n' * (p ^ t * m₀) ^ 2 = p ^ (2 * (s + t)) * (n' * m₀ ^ 2) := by
        ring
      rw [hidx, Top_even hrec hpn'' (s + t), Top_even hrec hpn' s, hχm]
      have hIH := h.cong (p * n') m₀ (by positivity) hm₀ hgood₀ (by
        intro q hq hqm
        rw [oddPart_mul_prime hp.out hn' hpn'] at hq
        rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp hq).1 with e | hq1
        · exact hpm₀ (e ▸ hqm)
        · exact hcop' q (Finset.mem_sdiff.mpr ⟨hq1, (Finset.mem_sdiff.mp hq).2⟩) hqm)
      rw [oddPart_mul_prime hp.out hn' hpn', Finset.insert_sdiff_of_notMem _ hpU,
        Finset.card_insert_of_notMem (fun h' => hnp (Finset.mem_sdiff.mp h').1)] at hIH
      have hb := h.bound (p * n')
      rw [oddPart_mul_prime hp.out hn' hpn', Finset.insert_sdiff_of_notMem _ hpU,
        Finset.card_insert_of_notMem (fun h' => hnp (Finset.mem_sdiff.mp h').1)] at hb
      have ho1 := odd_shell_diff_kappa_zero hpodd hap (s + t)
      have ho2 := odd_shell_diff_kappa_zero hpodd hap s
      set f₁ := shell ap p 0 (s + t) - shellPrev ap p 0 (s + t)
      set f₂ := shell ap p 0 s - shellPrev ap p 0 s
      have hev : Even (f₁ - f₂) := Odd.sub_odd ho1 ho2
      have hexp : χ p ^ (s + t) * (f₁ : R) * b (p * (n' * m₀ ^ 2)) -
          χ p ^ t * χ m₀ * (χ p ^ s * (f₂ : R) * b (p * n')) =
          χ p ^ (s + t) * ((f₁ : R) * (b (p * n' * m₀ ^ 2) - χ m₀ * b (p * n')) +
            ((f₁ - f₂ : ℤ) : R) * (χ m₀ * b (p * n'))) := by
        rw [show p * (n' * m₀ ^ 2) = p * n' * m₀ ^ 2 by ring]; push_cast; ring
      rw [hexp]
      apply dvd_mul_of_dvd_right
      apply dvd_add
      · apply dvd_mul_of_dvd_right
        convert hIH using 3; ring
      · refine two_pow_dvd_of_le ?_ (two_pow_dvd_intCast_even_mul hev
          (dvd_mul_of_dvd_right hb _))
        omega
    · -- `p ∈ J`: even factors `b_{s+1} − b_s ≡ d_0 (mod 4)`
      rw [oddPart_pow_odd_mul hp.out hn' hpn', Finset.insert_sdiff_insert,
        Finset.sdiff_insert_of_notMem hnp, hcard]
      have hidx : p ^ (2 * s + 1) * n' * (p ^ t * m₀) ^ 2 =
          p ^ (2 * (s + t) + 1) * (n' * m₀ ^ 2) := by ring
      rw [hidx, Top_odd hrec hpn'' (s + t), Top_odd hrec hpn' s, hχm,
        legendreSym_neg_mul_sq hpm₀]
      have hIH := h.cong n' m₀ hn' hm₀ hgood₀ hcop'
      have hb := h.bound n'
      have hκ := legendreSym_neg_eq_one_or hpn' hε
      set κ := ε * legendreSym p (-(n' : ℤ))
      have hd1 := shellDiff_modEq hκ hpodd hap (s + t)
      have hd2 := shellDiff_modEq hκ hpodd hap s
      set D₁ := shellDiff ap p κ (s + t)
      set D₀ := shellDiff ap p κ s
      have h4 : (4 : ℤ) ∣ D₁ - D₀ := Int.ModEq.dvd (hd2.1.trans hd1.1.symm)
      have hexp : χ p ^ (s + t + 1) * (D₁ : R) * b (n' * m₀ ^ 2) -
          χ p ^ t * χ m₀ * (χ p ^ (s + 1) * (D₀ : R) * b n') =
          χ p ^ (s + t + 1) * ((D₁ : R) * (b (n' * m₀ ^ 2) - χ m₀ * b n') +
            ((D₁ - D₀ : ℤ) : R) * (χ m₀ * b n')) := by
        push_cast; ring
      rw [hexp]
      apply dvd_mul_of_dvd_right
      apply dvd_add
      · exact two_pow_dvd_of_le (by omega) (two_pow_dvd_intCast_even_mul hd1.2 hIH)
      · exact two_pow_dvd_of_le (by omega)
          (two_pow_dvd_intCast_four_mul h4 (dvd_mul_of_dvd_right hb _))

end ZInQ.Manuscript.RC.Odd
