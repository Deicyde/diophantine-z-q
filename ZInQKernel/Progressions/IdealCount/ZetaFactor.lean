import ZInQKernel.Progressions.IdealCount.Splitting
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The Dedekind zeta function of a quadratic field as `ζ · L`

Let `K` be a quadratic field and `χ` a Dirichlet character with `χ(p) = ε_p` for every prime
`p` outside a finite set `P`. Comparing Euler products, for `re s > 1`,
`ζ_K(s) = ζ(s) L(s, χ) ∏_{p ∈ P} (1 - χ(p) p^(-s)) (1 - ε_p p^(-s))⁻¹`
(plan step 3.3, item 4). The Euler factor of `ζ_K` at `p` is
`∑_k a_K(p^k) p^(-ks) = (1 - p^(-s))⁻¹ (1 - ε_p p^(-s))⁻¹`, by item 2 and a Cauchy product.
-/

namespace ZInQ.Progressions

open NumberField Ideal Module Filter LSeries Complex

open scoped Topology

variable {K : Type*} [Field K] [NumberField K]

namespace IdealCount

/-! ### Convergence of the Dirichlet series of `a_K` -/

variable (K) in
theorem tendsto_sum_idealCount_div :
    Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.Icc 1 n, (idealCount K k : ℝ)) / n) atTop
      (𝓝 (dedekindZeta_residue K)) := by
  rw [dedekindZeta_residue_def]
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum, idealCount]
  congr
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem LSeriesSummable_idealCount {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (idealCount K n : ℂ)) s := by
  have := LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n ↦ (idealCount K n : ℝ))
    (Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using tendsto_sum_idealCount_div K))
    (fun n ↦ Nat.cast_nonneg _) zero_le_one hs
  simpa using this

/-! ### Multiplicativity of the terms -/

theorem term_idealCount_one (s : ℂ) : term (fun n ↦ (idealCount K n : ℂ)) s 1 = 1 := by
  simp [idealCount_one]

theorem term_idealCount_mul (s : ℂ) {m n : ℕ} (h : m.Coprime n) :
    term (fun n ↦ (idealCount K n : ℂ)) s (m * n) =
      term (fun n ↦ (idealCount K n : ℂ)) s m * term (fun n ↦ (idealCount K n : ℂ)) s n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero (mul_ne_zero hm hn), term_of_ne_zero hm, term_of_ne_zero hn,
    idealCount_mul K h, Nat.cast_mul, Nat.cast_mul, natCast_mul_natCast_cpow, mul_div_mul_comm]

/-- The Euler product of `ζ_K`. -/
theorem hasProd_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes ↦ ∑' e, term (fun n ↦ (idealCount K n : ℂ)) s (p ^ e))
      (dedekindZeta K s) := by
  rw [dedekindZeta_eq_LSeries_idealCount, LSeries]
  exact EulerProduct.eulerProduct_hasProd (term_idealCount_one s)
    (fun h ↦ term_idealCount_mul s h) (summable_norm_iff.mpr (LSeriesSummable_idealCount hs))
    (term_zero _ _)

/-! ### The Euler factors -/

theorem tsum_geom_sum_mul {ε x : ℂ} (hε : ‖ε‖ ≤ 1) (hx : ‖x‖ < 1) :
    ∑' e : ℕ, (∑ j ∈ Finset.range (e + 1), ε ^ j) * x ^ e = (1 - x)⁻¹ * (1 - ε * x)⁻¹ := by
  have hεx : ‖ε * x‖ < 1 := by
    rw [norm_mul]
    nlinarith [norm_nonneg ε, norm_nonneg x]
  have hs : ∀ {ξ : ℂ}, ‖ξ‖ < 1 → Summable fun n : ℕ ↦ ‖ξ ^ n‖ := fun h ↦ by
    simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) h
  rw [mul_comm, ← tsum_geometric_of_norm_lt_one hεx, ← tsum_geometric_of_norm_lt_one hx,
    tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (hs hεx) (hs hx)]
  refine tsum_congr fun e ↦ ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk' : k ≤ e := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' hk']

theorem natCast_pow_cpow (p e : ℕ) (s : ℂ) : ((p ^ e : ℕ) : ℂ) ^ s = ((p : ℂ) ^ s) ^ e := by
  induction e with
  | zero => simp
  | succ e ih => rw [pow_succ, Nat.cast_mul, natCast_mul_natCast_cpow, ih, pow_succ]

theorem norm_natCast_cpow_neg_lt_one {p : ℕ} (hp : 1 < p) {s : ℂ} (hs : 0 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_natCast_cpow_of_pos (by omega), neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp) (by linarith)

theorem norm_localEps_le_one (h2 : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) :
    ‖(localEps K p : ℂ)‖ ≤ 1 := by
  rcases localEps_mem h2 hp with h | h | h <;> simp [h]

/-- The Euler factor of `ζ_K` at `p` is `(1 - p^(-s))⁻¹ (1 - ε_p p^(-s))⁻¹`. -/
theorem tsum_term_idealCount_prime_pow (h2 : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) {s : ℂ}
    (hs : 0 < s.re) :
    ∑' e, term (fun n ↦ (idealCount K n : ℂ)) s (p ^ e) =
      (1 - (p : ℂ) ^ (-s))⁻¹ * (1 - localEps K p * (p : ℂ) ^ (-s))⁻¹ := by
  rw [← tsum_geom_sum_mul (norm_localEps_le_one h2 hp)
    (norm_natCast_cpow_neg_lt_one hp.one_lt hs)]
  refine tsum_congr fun e ↦ ?_
  have h := congrArg (Int.cast : ℤ → ℂ) (idealCount_prime_pow h2 hp e)
  push_cast at h
  rw [term_of_ne_zero (pow_ne_zero _ hp.ne_zero), h, natCast_pow_cpow, cpow_neg, inv_pow,
    div_eq_mul_inv]

end IdealCount

open IdealCount

/-- **Factorization of `ζ_K`** (plan step 3.3, item 4), for a finite set `P` of primes outside
which `ε_p = χ(p)`. -/
theorem dedekindZeta_eq_mul_prod_of_localEps_eq (h2 : finrank ℚ K = 2) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hχ : ∀ p : ℕ, p.Prime → p ∉ P → (localEps K p : ℂ) = χ p) {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s * LSeries (fun n ↦ χ n) s *
      ∏ p ∈ P, (1 - χ p * (p : ℂ) ^ (-s)) * (1 - localEps K p * (p : ℂ) ^ (-s))⁻¹ := by
  classical
  set f : ℕ → ℂ := fun p ↦ (1 - χ p * (p : ℂ) ^ (-s)) * (1 - localEps K p * (p : ℂ) ^ (-s))⁻¹
  have hs0 : 0 < s.re := by linarith
  have hR : HasProd (fun p : Nat.Primes ↦ if (p : ℕ) ∈ P then f p else 1) (∏ p ∈ P, f p) := by
    have : HasProd (fun p : Nat.Primes ↦ if (p : ℕ) ∈ P then f p else 1)
        (∏ b ∈ (P.subtype Nat.Prime : Finset Nat.Primes), if (b : ℕ) ∈ P then f b else 1) :=
      hasProd_prod_of_ne_finset_one fun b hb ↦ by
        have hb' : (b : ℕ) ∉ P := fun h ↦ hb (Finset.mem_subtype.mpr h)
        simp [hb']
    convert this using 1
    calc ∏ p ∈ P, f p = ∏ p ∈ P with p.Prime, (if p ∈ P then f p else 1) := by
          rw [Finset.filter_true_of_mem hP]
          exact Finset.prod_congr rfl fun p hp ↦ by simp [hp]
      _ = _ := (Finset.prod_subtype_eq_prod_filter (fun p ↦ if p ∈ P then f p else 1)).symm
  have H := ((riemannZeta_eulerProduct_hasProd hs).mul
    (DirichletCharacter.LSeries_eulerProduct_hasProd χ hs)).mul hR
  have E := hasProd_dedekindZeta (K := K) hs
  refine E.unique (H.congr_fun ?_)
  intro p
  rw [tsum_term_idealCount_prime_pow h2 p.prop hs0]
  have hne : (1 : ℂ) - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
    refine sub_ne_zero.mpr fun h ↦ ?_
    have := norm_natCast_cpow_neg_lt_one p.prop.one_lt hs0
    have h1 : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul]
      nlinarith [χ.norm_le_one p, norm_nonneg (χ p), norm_nonneg ((p : ℂ) ^ (-s))]
    rw [← h, norm_one] at h1
    exact lt_irrefl _ h1
  split_ifs with hp
  · simp only [f]
    rw [mul_assoc, ← mul_assoc (1 - χ p * (p : ℂ) ^ (-s))⁻¹, inv_mul_cancel₀ hne, one_mul]
  · rw [hχ p p.prop hp, mul_one]

/-- **Factorization of `ζ_K`** (plan step 3.3, item 4), in the form used by step 3.4: `χ` a
Dirichlet character mod `q`, `P` the primes dividing `2 q`, and `s > 1` real. -/
theorem dedekindZeta_eq_riemannZeta_mul_LSeries_mul_prod (h2 : finrank ℚ K = 2) {q : ℕ}
    (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    (hχ : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q → (localEps K p : ℂ) = χ p) {s : ℝ} (hs : 1 < s) :
    dedekindZeta K s = riemannZeta s * LSeries (fun n ↦ χ n) s *
      ∏ p ∈ (2 * q).primeFactors,
        (1 - χ p * (p : ℂ) ^ (-(s : ℂ))) * (1 - localEps K p * (p : ℂ) ^ (-(s : ℂ)))⁻¹ :=
  dedekindZeta_eq_mul_prod_of_localEps_eq h2 χ _ (fun _ hp ↦ Nat.prime_of_mem_primeFactors hp)
    (fun p hp hpP ↦ hχ p hp fun hdvd ↦ hpP (Nat.mem_primeFactors.mpr ⟨hp, hdvd, by omega⟩))
    (by simpa using hs)

/-- Item 4 combined with the splitting law (item 3): if `α ^ 2 = d` with `d` not a square, every
prime `p ∤ 2 q` is prime to `d`, and `χ(p) = (d / p)` for those primes, then
`ζ_K(s) = ζ(s) L(s, χ) ∏_{p ∣ 2q} (1 - χ(p) p^(-s)) (1 - ε_p p^(-s))⁻¹` for real `s > 1`. -/
theorem dedekindZeta_eq_riemannZeta_mul_LSeries_mul_prod_of_legendreSym
    (h2 : finrank ℚ K = 2) {α : 𝓞 K} {d : ℤ} (hα : α ^ 2 = d) (hd : ¬ IsSquare d) {q : ℕ}
    (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    (hdq : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * q → ¬ (p : ℤ) ∣ d)
    (hχ : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ 2 * q → χ p = legendreSym p d) {s : ℝ} (hs : 1 < s) :
    dedekindZeta K s = riemannZeta s * LSeries (fun n ↦ χ n) s *
      ∏ p ∈ (2 * q).primeFactors,
        (1 - χ p * (p : ℂ) ^ (-(s : ℂ))) * (1 - localEps K p * (p : ℂ) ^ (-(s : ℂ)))⁻¹ := by
  refine dedekindZeta_eq_riemannZeta_mul_LSeries_mul_prod h2 hq χ (fun p hp hpq ↦ ?_) hs
  have := Fact.mk hp
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact hpq (dvd_mul_right 2 q)
  rw [localEps_eq_legendreSym h2 hα hd p hp2 (hdq p hp hpq), hχ p hpq]

end ZInQ.Progressions
