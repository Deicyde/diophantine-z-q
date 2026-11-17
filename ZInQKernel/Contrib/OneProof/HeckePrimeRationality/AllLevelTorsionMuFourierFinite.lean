import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionMuFourier

/-!
# Finite inversion and unrestricted labels for actual μ/x duality

Character orthogonality gives the inverse with normalization minus 1/N². The
zero-row normalization uses the proved vanishing sum of actual Weierstrass
values and the actual zero extension. Integer labels are reduced by Euclidean
remainders only after their nonnegativity is established.
-/

noncomputable section
set_option autoImplicit false
open Complex UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionMuFourier

open TorsionWeierstrassData TorsionFourierComparison

variable (N : ℕ) [NeZero N]

/-- The same alternating torsion character, with finite pairs bundled. -/
def chi (p r : Fin N × Fin N) : ℂ := character N (p.1 : ℕ) (p.2 : ℕ) (r.1 : ℕ) (r.2 : ℕ)

/-- A finite linear transform; the actual torsion values are not defined by it. -/
def transform (f : Fin N × Fin N → ℂ) (r : Fin N × Fin N) : ℂ := ∑ p, f p * chi N p r

private lemma finite_dvd_sub (p q : Fin N) :
    (N : ℤ) ∣ ((p : ℕ) : ℤ) - ((q : ℕ) : ℤ) ↔ p = q := by
  constructor
  · intro h
    have hc := (ZMod.intCast_eq_intCast_iff_dvd_sub ((q : ℕ) : ℤ) ((p : ℕ) : ℤ) N).mpr h
    have he : (q : ℕ) = (p : ℕ) := by
      have hv := congrArg ZMod.val hc
      simpa only [Int.cast_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt p.isLt,
        Nat.mod_eq_of_lt q.isLt] using hv
    exact (Fin.ext he).symm
  · rintro rfl
    simp

private lemma chi_composition (q r p : Fin N × Fin N) : chi N q r * chi N r p =
    character N (r.1 : ℕ) (r.2 : ℕ)
      (((p.1 : ℕ) : ℤ) - ((q.1 : ℕ) : ℤ)) (((p.2 : ℕ) : ℤ) - ((q.2 : ℕ) : ℤ)) := by
  unfold chi character
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma chi_orthogonality (q p : Fin N × Fin N) :
    (∑ r, chi N q r * chi N r p) = if q = p then (N : ℂ) ^ 2 else 0 := by
  rw [Fintype.sum_prod_type]
  simp_rw [chi_composition]
  rw [character_sum N]
  have he : ((N : ℤ) ∣ ((p.1 : ℕ) : ℤ) - ((q.1 : ℕ) : ℤ) ∧
      (N : ℤ) ∣ ((p.2 : ℕ) : ℤ) - ((q.2 : ℕ) : ℤ)) ↔ q = p := by
    rw [finite_dvd_sub, finite_dvd_sub]
    constructor
    · intro h
      exact (Prod.ext h.1 h.2).symm
    · rintro rfl
      exact ⟨rfl, rfl⟩
  simp only [he]

lemma transform_square (f : Fin N × Fin N → ℂ) (r : Fin N × Fin N) :
    transform N (transform N f) r = (N : ℂ) ^ 2 * f r := by
  unfold transform
  simp only [Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, chi_orthogonality]
  simp [mul_ite, mul_comm]

lemma transform_zero (f : Fin N × Fin N → ℂ) : transform N f (0, 0) = ∑ p, f p := by
  simp [transform, chi, character]

/-- The actual Weierstrass distribution theorem supplies the zero sum, not a Fourier assumption. -/
lemma x_sum_zero (τ : ℍ) : (∑ p : Fin N × Fin N, xValue N (p.1 : ℕ) (p.2 : ℕ) τ) = 0 := by
  rw [Fintype.sum_prod_type]
  have h := WeierstrassDistributionNat.x_distribution_nat N 1 (NeZero.pos N) one_pos τ 0 0
  simpa only [Nat.mul_one, Nat.cast_one, zero_add, one_mul, xValue_zero, mul_zero] using h

private lemma transform_mu_good (τ : ℍ) (q : Fin N × Fin N) (hq : q ≠ (0, 0)) :
    transform N (fun p => muValue N (p.1 : ℕ) (p.2 : ℕ) τ) q = -xValue N (q.1 : ℕ) (q.2 : ℕ) τ := by
  have hg : ¬ ((N : ℤ) ∣ ((q.1 : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((q.2 : ℕ) : ℤ)) := by
    apply (finite_good_iff N q.1 q.2).mpr
    by_contra h
    have hz : q.1 = 0 ∧ q.2 = 0 := by tauto
    exact hq (Prod.ext hz.1 hz.2)
  have hx := x_fourier_finite_good N τ q.1 q.2 hg
  have he : xValue N (q.1 : ℕ) (q.2 : ℕ) τ =
      -transform N (fun p => muValue N (p.1 : ℕ) (p.2 : ℕ) τ) q := by
    simpa only [transform, chi, Fintype.sum_prod_type] using hx
  linear_combination he

/-- Orthogonality, the actual μ zero value, and the proved x zero sum fix the missing zero row. -/
lemma transform_mu_zero (τ : ℍ) :
    transform N (fun p => muValue N (p.1 : ℕ) (p.2 : ℕ) τ) (0, 0) = 0 := by
  let f : Fin N × Fin N → ℂ := fun p => muValue N (p.1 : ℕ) (p.2 : ℕ) τ
  let X : Fin N × Fin N → ℂ := fun p => xValue N (p.1 : ℕ) (p.2 : ℕ) τ
  let p0 : Fin N × Fin N := (0, 0)
  have hs : (∑ q, transform N f q) = 0 := by
    have he := transform_square N f p0
    rw [transform_zero] at he
    simpa only [f, p0, Fin.val_zero, Nat.cast_zero, muValue_zero, mul_zero] using he
  have hx : (∑ q, X q) = 0 := x_sum_zero N τ
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p0)] at hs hx
  have hx0 : X p0 = 0 := by simp only [X, p0, Fin.val_zero, Nat.cast_zero, xValue_zero]
  rw [hx0, zero_add] at hx
  have hb : (∑ q ∈ Finset.univ.erase p0, transform N f q) = 0 := by
    calc
      _ = -∑ q ∈ Finset.univ.erase p0, X q := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro q hq
        exact transform_mu_good N τ q (Finset.ne_of_mem_erase hq)
      _ = 0 := by rw [hx, neg_zero]
  rw [hb, add_zero] at hs
  exact hs

/-- The forward actual weight-two transform, including the zero finite class. -/
theorem x_fourier_finite (τ : ℍ) (r s : Fin N) : xValue N (r : ℕ) (s : ℕ) τ =
    -∑ a : Fin N, ∑ b : Fin N, muValue N (a : ℕ) (b : ℕ) τ *
      character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ) := by
  have he : xValue N (r : ℕ) (s : ℕ) τ =
      -transform N (fun p => muValue N (p.1 : ℕ) (p.2 : ℕ) τ) (r, s) := by
    by_cases hz : (r, s) = (0, 0)
    · have hrs := Prod.mk.inj hz
      obtain ⟨rfl, rfl⟩ := hrs
      simp only [Fin.val_zero, Nat.cast_zero, xValue_zero, transform_mu_zero, neg_zero]
    · have hg := transform_mu_good N τ (r, s) hz
      linear_combination hg
  simpa only [transform, chi, Fintype.sum_prod_type] using he

/-- Inverse actual weight-two transform with the exact normalization minus 1/N². -/
theorem mu_fourier_finite (τ : ℍ) (r s : Fin N) : muValue N (r : ℕ) (s : ℕ) τ =
    -(1 / (N : ℂ) ^ 2) * ∑ a : Fin N, ∑ b : Fin N, xValue N (a : ℕ) (b : ℕ) τ *
      character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ) := by
  let f : Fin N × Fin N → ℂ := fun p => muValue N (p.1 : ℕ) (p.2 : ℕ) τ
  let X : Fin N × Fin N → ℂ := fun p => xValue N (p.1 : ℕ) (p.2 : ℕ) τ
  have hx : X = fun q => -transform N f q := by
    funext q
    simpa only [X, f, transform, chi, Fintype.sum_prod_type] using x_fourier_finite N τ q.1 q.2
  have hT : transform N X (r, s) = -(N : ℂ) ^ 2 * f (r, s) := by
    rw [hx]
    calc
      _ = -transform N (transform N f) (r, s) := by
        simp only [transform, neg_mul, Finset.sum_neg_distrib]
      _ = _ := by rw [transform_square]; ring
  have he : f (r, s) = -(1 / (N : ℂ) ^ 2) * transform N X (r, s) := by
    rw [hT]
    have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    field_simp [hN]
  simpa only [f, X, transform, chi, Fintype.sum_prod_type] using he

lemma muValue_shift (a b m n : ℤ) (τ : ℍ) :
    muValue N (a + (N : ℤ) * m) (b + (N : ℤ) * n) τ = muValue N a b τ := by
  unfold muValue lambdaValue
  rw [reg_shift, WeierstrassDistributionNat.xValue_shift (NeZero.pos N)]

private lemma integer_representative (r : ℤ) : ∃ R : Fin N, ∃ m : ℤ, r = ((R : ℕ) : ℤ) + (N : ℤ) * m := by
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hNz : (0 : ℤ) < N := by exact_mod_cast NeZero.pos N
  let R : Fin N := ⟨(r % (N : ℤ)).toNat, by
    have h0 := Int.emod_nonneg r hN0
    have h1 := Int.emod_lt_of_pos r hNz
    omega⟩
  have hR : ((R : ℕ) : ℤ) = r % (N : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg r hN0)
  refine ⟨R, r / (N : ℤ), ?_⟩
  rw [hR]
  exact (Int.emod_add_mul_ediv r (N : ℤ)).symm

/-- Actual x/μ forward Fourier duality for every integer row, with orientation br−as. -/
theorem x_fourier_duality (τ : ℍ) (r s : ℤ) : xValue N r s τ =
    -∑ a : Fin N, ∑ b : Fin N, muValue N (a : ℕ) (b : ℕ) τ *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        (((b : ℕ) : ℂ) * (r : ℂ) - ((a : ℕ) : ℂ) * (s : ℂ)) / (N : ℂ)) := by
  obtain ⟨R, m, hr⟩ := integer_representative N r
  obtain ⟨S, n, hs⟩ := integer_representative N s
  change xValue N r s τ = -∑ a : Fin N, ∑ b : Fin N, muValue N (a : ℕ) (b : ℕ) τ *
    character N (a : ℕ) (b : ℕ) r s
  rw [hr, hs, WeierstrassDistributionNat.xValue_shift (NeZero.pos N)]
  simp_rw [character_shift]
  exact x_fourier_finite N τ R S

/-- Actual μ/x inverse Fourier duality for every integer row, normalized by minus 1/N². -/
theorem mu_fourier_duality (τ : ℍ) (r s : ℤ) : muValue N r s τ =
    -(1 / (N : ℂ) ^ 2) * ∑ a : Fin N, ∑ b : Fin N, xValue N (a : ℕ) (b : ℕ) τ *
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I *
        (((b : ℕ) : ℂ) * (r : ℂ) - ((a : ℕ) : ℂ) * (s : ℂ)) / (N : ℂ)) := by
  obtain ⟨R, m, hr⟩ := integer_representative N r
  obtain ⟨S, n, hs⟩ := integer_representative N s
  change muValue N r s τ = -(1 / (N : ℂ) ^ 2) * ∑ a : Fin N, ∑ b : Fin N,
    xValue N (a : ℕ) (b : ℕ) τ * character N (a : ℕ) (b : ℕ) r s
  rw [hr, hs, muValue_shift]
  simp_rw [character_shift]
  exact mu_fourier_finite N τ R S

end ZInQ.Contrib.HeckePrimeRationality.TorsionMuFourier
