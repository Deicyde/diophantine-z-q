import ZInQKernel.Multiplication.Certificate.Constants
import ZInQKernel.Hypotheses.HeightMin
import ZInQKernel.Multiplication.Certificate.ClearingArithmetic
import ZInQKernel.Hypotheses.Pole
import ZInQKernel.Size.FormalMultiple.Existence

/-!
# Properties of the multiplication constants

Blueprint: `multiplication/certificate/constants-properties.md`.

1. `M₀ ≥ 1` (`one_le_M0_spec`), so `c_* ≥ 4`; `ℓ₀ ≥ 1`.
2. `S_mul` is a finite set of primes containing every prime `p ≤ 324`, `p ≤ R` for `p ∈ S_mul`,
   `R ≥ D` and `R ≥ 10¹²` (`S_mul_admissible`); the six-contact constant at `R` is
   `H₆(S_mul; R) = A_ht` (`Aht_eq_heightH6`), so the estimate reads
   `h(u) ≤ A_ht M_{S_mul}(u)²⁴` (`sixContact_at_Smul`, from the minimal hypothesis
   `SixContactMin` and `H₆(D) ≤ H₆(R)`).
3. `A_ht ≥ 2·10¹³`, `48 A_ht ≥ 1`, `T > 4`.
4. The catalogue primes exceed `324` and are distinct, `H_cat` is squarefree with prime factors
   `𝓗`, and `v_p(ℓ₀) = E_p` for `p ∈ S_b`, `v_p(ℓ₀) = 0` otherwise (`padicValNat_ell`).
5. A prime `p ∉ S_mul` has `p > 324`, `p ∤ c_*`, `p ∤ ℓ₀`, `p ∉ S₀` (`not_mem_S_mul`).

The syntax chapter's constants `Syntax.D`, `Syntax.E0`, `Syntax.Bcm`, `Syntax.Ccm` and the
hypothesis file's `heightD`, `heightE0`, `heightBcm`, `heightCcm` are separate definitions; they
are identified through their equation lemmas only (`D_eq_heightD`, …): unfolding either side
would make the kernel evaluate them.

Positivity of `M₀` is the success of the least-formal-multiple search, proved in the size
chapter (`Size.M0_bounds`); `one_le_M0` derives it from any successful formal multiple and
`one_le_M0_spec` is the instance. Without it `c_* = 0`, and every prime divides `c_*`.
-/

namespace ZInQ.Mult

open scoped BigOperators

/-! ### The height constants of the two chapters agree -/

/-- `D` of the specification is the `D` of hypothesis H. -/
theorem D_eq_heightD : Syntax.D = heightD := by
  rw [Syntax.D_eq, Compiler.Precision.heightD_eq, Syntax.F_eq, Compiler.Precision.heightF0_eq]

theorem heightG0_eq_lit : heightG0 = 116064000000 := rfl

theorem E0_eq_heightE0 : Syntax.E0 = heightE0 := by
  rw [Syntax.E0_eq, Compiler.Precision.heightE0_eq, D_eq_heightD, Syntax.G0_eq, heightG0_eq_lit]

theorem Bcm_eq_heightBcm : Syntax.Bcm = heightBcm := by
  rw [Syntax.Bcm_eq, Compiler.Precision.heightBcm_eq, D_eq_heightD]

theorem Ccm_eq_heightCcm : Syntax.Ccm = heightCcm := by
  rw [Syntax.Ccm_eq, Compiler.Precision.heightCcm_eq, Bcm_eq_heightBcm, D_eq_heightD]

/-- `r^(r e)` as a real power with real exponent, for variables (nothing is evaluated). -/
theorem rpow_mul_self_natCast (r e : ℕ) :
    (r : ℝ) ^ ((r : ℝ) * (e : ℝ)) = ((r ^ (r * e) : ℕ) : ℝ) := by
  rw [Nat.cast_pow, ← Real.rpow_natCast, Nat.cast_mul]

/-- The real power `Q_R = R^(R E₀)` is the natural power `Q`. -/
theorem heightQ_R : heightQ (Syntax.R : ℝ) = (Syntax.Q : ℝ) := by
  rw [heightQ, ← E0_eq_heightE0, rpow_mul_self_natCast, Syntax.Q_eq]

/-- The cast of `2·10¹³ max(max(1, c), q¹⁷)`, for variables. -/
theorem cast_aht_formula (c q : ℕ) : ((2 * 10 ^ 13 * max (max 1 c) (q ^ 17) : ℕ) : ℝ) =
    2 * 10 ^ 13 * max 1 (max (c : ℝ) ((q : ℝ) ^ 17)) := by
  rw [max_assoc]; push_cast; norm_num

/-- **`H₆(S_mul; R) = A_ht`** as real numbers. -/
theorem Aht_eq_heightH6 : (Syntax.Aht : ℝ) = heightH6 (Syntax.R : ℝ) := by
  rw [heightH6, heightQ_R, Syntax.Aht_eq, Ccm_eq_heightCcm, cast_aht_formula]

/-! ### Item 1 -/

/-- `M₀ ≥ 1`, given a successful formal multiple for `N_s`. -/
theorem one_le_M0 (h : ∃ m, 1 ≤ m ∧ Syntax.FormalCondition Syntax.Ns m) : 1 ≤ Syntax.M0 :=
  (Syntax.M0_spec h).1

/-- `M₀ ≥ 1`: `N_s ≥ 1` has a formal multiple (`Size.M0_bounds`). -/
theorem one_le_M0_spec : 1 ≤ Syntax.M0 := (Size.M0_bounds Syntax.Ns_pos).1

theorem four_le_cstar : 4 ≤ Syntax.cstar := by
  have := one_le_M0_spec
  rw [Syntax.cstar_eq]; omega

theorem cstar_pos : 0 < Syntax.cstar :=
  lt_of_lt_of_le (by norm_num) four_le_cstar

theorem one_le_ell : 1 ≤ Syntax.ell := Syntax.ell_pos

/-! ### The prime sets -/

theorem prime_of_mem_catalogue {p : ℕ} (hp : p ∈ catalogue) : p.Prime ∧ 324 < p := by
  obtain ⟨r, i, hr, hcop, -, h⟩ := mem_catalogue.1 hp
  rw [h]
  exact ⟨(cataloguePrime_spec hr hcop i).1, (cataloguePrime_spec hr hcop i).2.1⟩

theorem lt_of_mem_catalogue {p : ℕ} (hp : p ∈ catalogue) : 324 < p :=
  (prime_of_mem_catalogue hp).2

theorem not_mem_catalogue_of_mem_S_ht {p : ℕ} (hp : p ∈ S_ht) : p ∉ catalogue := fun h =>
  absurd (mem_S_ht.1 hp).2 (not_le.2 (lt_of_mem_catalogue h))

theorem prime_of_mem_S_b {p : ℕ} (hp : p ∈ S_b) : p.Prime := by
  rcases mem_S_b.1 hp with h | h
  · exact (mem_S_ht.1 h).1
  · exact (prime_of_mem_catalogue h).1

theorem prime_of_mem_S_mul {p : ℕ} (hp : p ∈ S_mul) : p.Prime := by
  rcases mem_S_mul.1 hp with h | h | h
  · exact (mem_S_ht.1 h).1
  · exact (prime_of_mem_catalogue h).1
  · exact h.1

theorem mem_S_mul_of_le {p : ℕ} (hp : p.Prime) (h : p ≤ 324) : p ∈ S_mul :=
  mem_S_mul.2 (Or.inl (mem_S_ht.2 ⟨hp, h⟩))

theorem le_R_of_mem_S_mul {p : ℕ} (hp : p ∈ S_mul) : p ≤ Syntax.R := by
  rcases mem_S_mul.1 hp with h | h | ⟨-, hd, hc⟩
  · exact (mem_S_ht.1 h).2.trans (le_trans (by norm_num) Syntax.ten_pow_twelve_le_R)
  · exact (Syntax.le_Hmax_of_mem_catalogueSet (mem_catalogue.1 h)).trans Syntax.Hmax_le_R
  · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hc) hd).trans Syntax.cstar_le_R

/-- **Item 2.** `S = S_mul` and `R = max(D, H_max, c_*, 10¹²)` are admissible in hypothesis H. -/
theorem S_mul_admissible :
    (∀ p ∈ S_mul, p.Prime) ∧ (∀ p : ℕ, p.Prime → p ≤ 324 → p ∈ S_mul) ∧
      (heightD : ℝ) ≤ Syntax.R ∧ (∀ p ∈ S_mul, (p : ℝ) ≤ Syntax.R) ∧
      (10 : ℝ) ^ 12 ≤ Syntax.R :=
  ⟨fun _ hp => prime_of_mem_S_mul hp, fun _ hp h => mem_S_mul_of_le hp h,
    by rw [← D_eq_heightD]; exact_mod_cast Syntax.D_le_R,
    fun _ hp => by exact_mod_cast le_R_of_mem_S_mul hp,
    by exact_mod_cast Syntax.ten_pow_twelve_le_R⟩

/-- **The six-contact estimate at `S = S_mul`, `R = max(D, H_max, c_*, 10¹²)`:**
`h(u) ≤ A_ht M_{S_mul}(u)²⁴` for `u ∉ 𝒞`, from `SixContactMin` since `H₆(D) ≤ H₆(R) = A_ht`. -/
theorem sixContact_at_Smul (hH : SixContactMin) {u : ℚ} (hu : u ∉ contactSet) :
    ratHeight u ≤ (Syntax.Aht : ℝ) * (contactSupport S_mul u : ℝ) ^ 24 := by
  rewrite [Aht_eq_heightH6]
  have hD : (1 : ℝ) ≤ heightD := by
    exact_mod_cast le_trans (by norm_num) Compiler.Precision.ten_pow_twelve_le_heightD
  exact (hH u hu).trans (mul_le_mul_of_nonneg_right
    (heightH6_mono_of_one_le hD S_mul_admissible.2.2.1) (by positivity))

/-! ### Item 3 -/

theorem one_le_forty_eight_mul_Aht : 1 ≤ 48 * Syntax.Aht := by
  have := Syntax.Aht_pos; omega

theorem four_lt_T : 4 < Syntax.T := by
  have := Syntax.two_mul_ten_pow_thirteen_le_Aht
  have := Syntax.Aht_le_T
  omega

/-! ### Item 4: the valuations of `ℓ₀` -/

/-- `v_p(∏_{q ∈ s} q) = [p ∈ s]` for a finite set `s` of primes. -/
theorem padicValNat_prod_primes {s : Finset ℕ} (hs : ∀ q ∈ s, q.Prime) {p : ℕ} (hp : p.Prime) :
    padicValNat p (∏ q ∈ s, q) = if p ∈ s then 1 else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (Finset.mem_insert_of_mem hq)
    have hpa : (a : ℕ).Prime := hs a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, padicValNat.mul hpa.ne_zero
      (Finset.prod_ne_zero_iff.2 fun q hq => (hs' q hq).ne_zero), ih hs']
    have : Fact a.Prime := ⟨hpa⟩
    by_cases hpa' : p = a
    · subst hpa'
      simp [ha, padicValNat_self]
    · rw [padicValNat_primes hpa']
      simp [hpa', Finset.mem_insert]

theorem Ps_eq_prod : Syntax.Ps = ∏ p ∈ S_ht, p := by
  rw [Syntax.Ps_eq]
  rfl

theorem Hcat_eq_prod : Syntax.Hcat = ∏ p ∈ catalogue, p := by
  rw [catalogue_eq]; exact Syntax.Hcat_eq_prod_catalogueSet.1

theorem padicValNat_Ps {p : ℕ} (hp : p.Prime) :
    padicValNat p Syntax.Ps = if p ∈ S_ht then 1 else 0 := by
  rw [Ps_eq_prod, padicValNat_prod_primes (fun q hq => (mem_S_ht.1 hq).1) hp]

theorem padicValNat_Hcat {p : ℕ} (hp : p.Prime) :
    padicValNat p Syntax.Hcat = if p ∈ catalogue then 1 else 0 := by
  rw [Hcat_eq_prod, padicValNat_prod_primes (fun q hq => (prime_of_mem_catalogue hq).1) hp]

/-- Distinct catalogue positions give distinct primes. -/
theorem catalogue_injective {r r' i i' : ℕ} (hr : r < catalogueModulus)
    (hcop : Nat.Coprime r catalogueModulus) (hr' : r' < catalogueModulus)
    (hcop' : Nat.Coprime r' catalogueModulus) (h : cataloguePrime r i = cataloguePrime r' i') :
    r = r' ∧ i = i' := by
  rw [Syntax.cataloguePrime_catalogueModulus, Syntax.cataloguePrime_catalogueModulus] at h
  exact Syntax.cataloguePrime_injOn (Syntax.mem_unitResidues_catalogueModulus.2 ⟨hr, hcop⟩)
    (Syntax.mem_unitResidues_catalogueModulus.2 ⟨hr', hcop'⟩) h

/-- `H_cat` is squarefree with set of prime factors `𝓗`. -/
theorem Hcat_squarefree : Squarefree Syntax.Hcat ∧ Syntax.Hcat.primeFactors = catalogue := by
  have hne : Syntax.Hcat ≠ 0 := Syntax.Hcat_pos.ne'
  refine ⟨?_, ?_⟩
  · rw [Nat.squarefree_iff_factorization_le_one hne]
    intro p
    by_cases hp : p.Prime
    · rw [Nat.factorization_def _ hp, padicValNat_Hcat hp]
      split_ifs <;> norm_num
    · rw [Nat.factorization_eq_zero_of_not_prime _ hp]; norm_num
  · ext p
    rw [Nat.mem_primeFactors]
    constructor
    · rintro ⟨hp, hd, -⟩
      have : Fact p.Prime := ⟨hp⟩
      have h1 := (dvd_iff_padicValNat_ne_zero hne).1 hd
      rw [padicValNat_Hcat hp] at h1
      by_contra hc
      exact h1 (ite_eq_right hc)
    · intro hp
      exact ⟨(prime_of_mem_catalogue hp).1, Hcat_eq_prod ▸ Finset.dvd_prod_of_mem _ hp, hne⟩

/-- `v_p(12 a^2916 b^732)` for variables `a, b ≠ 0`. Stated for variables so that the
instance-path checks of the power never meet the constants `P_s`, `H_cat`. -/
theorem padicValNat_ell_formula {p a b : ℕ} [Fact p.Prime] (ha : a ≠ 0) (hb : b ≠ 0) :
    padicValNat p (12 * (a ^ 2916 * b ^ 732)) =
      padicValNat p 12 + (2916 * padicValNat p a + 732 * padicValNat p b) := by
  rw [padicValNat.mul (by norm_num) (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb)),
    padicValNat.mul (pow_ne_zero _ ha) (pow_ne_zero _ hb), padicValNat.pow, padicValNat.pow]

/-- **`v_p(ℓ₀) = E_p` for `p ∈ S_b`, `v_p(ℓ₀) = 0` otherwise.** -/
theorem padicValNat_ell {p : ℕ} (hp : p.Prime) :
    padicValNat p Syntax.ell = if p ∈ S_b then Ep p else 0 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Syntax.ell_eq, padicValNat_ell_formula Syntax.Ps_pos.ne' Syntax.Hcat_pos.ne',
    padicValNat_Ps hp, padicValNat_Hcat hp]
  by_cases h1 : p ∈ S_ht
  · have h2 := not_mem_catalogue_of_mem_S_ht h1
    rw [ite_eq_left h1, ite_eq_right h2, ite_eq_left (mem_S_b.2 (Or.inl h1)), Ep, Cp,
      Bp_of_mem_S_ht h1]
    omega
  · have h5 : 5 ≤ p := by
      by_contra h
      exact h1 (mem_S_ht.2 ⟨hp, by omega⟩)
    rw [ite_eq_right h1, padicValNat_twelve_of_five_le hp h5]
    by_cases h2 : p ∈ catalogue
    · rw [ite_eq_left h2, ite_eq_left (mem_S_b.2 (Or.inr h2)), Ep, Cp, Bp_of_not_mem_S_ht h1,
        padicValNat_twelve_of_five_le hp h5]
    · rw [ite_eq_right h2, ite_eq_right (by rw [mem_S_b]; tauto)]

theorem padicValNat_ell_of_mem {p : ℕ} (hp : p ∈ S_b) : padicValNat p Syntax.ell = Ep p := by
  rw [padicValNat_ell (prime_of_mem_S_b hp), ite_eq_left hp]

theorem padicValNat_ell_of_not_mem {p : ℕ} (hp : p.Prime) (h : p ∉ S_b) :
    padicValNat p Syntax.ell = 0 := by
  rw [padicValNat_ell hp, ite_eq_right h]

/-! ### Item 5 -/

/-- **Primes outside `S_mul`.** A prime `p ∉ S_mul` satisfies `p > 324`,
`p ∤ c_*`, `p ∤ ℓ₀` and `p ∉ S₀ = {2, 3, 5, 7, 13}`. -/
theorem not_mem_S_mul {p : ℕ} (hp : p.Prime) (h : p ∉ S_mul) :
    324 < p ∧ ¬ p ∣ Syntax.cstar ∧ ¬ p ∣ Syntax.ell ∧ p ∉ poleS0 := by
  have h324 : 324 < p := by
    by_contra hle
    exact h (mem_S_mul_of_le hp (by omega))
  refine ⟨h324, fun hd => h (mem_S_mul.2 (Or.inr (Or.inr ⟨hp, hd, cstar_pos.ne'⟩))),
    fun hd => ?_, fun h0 => ?_⟩
  · have : Fact p.Prime := ⟨hp⟩
    have hb : p ∉ S_b := fun hb => h (S_b_subset_S_mul hb)
    exact (dvd_iff_padicValNat_ne_zero Syntax.ell_pos.ne').1 hd (padicValNat_ell_of_not_mem hp hb)
  · simp only [poleS0, Finset.mem_insert, Finset.mem_singleton] at h0
    omega

end ZInQ.Mult
