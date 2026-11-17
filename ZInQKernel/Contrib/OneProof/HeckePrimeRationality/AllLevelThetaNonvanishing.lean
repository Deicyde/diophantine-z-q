import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionDefinitions
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.ThetaFiveNonvanishing
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Nonvanishing of the odd theta function at nonzero torsion points of every level

For every positive level `N`, every `τ` in the upper half-plane and all integers `a, b` that are
not both divisible by `N`, Mathlib's two-variable theta function `jacobiTheta₂` does not vanish
at `(a τ + b)/N + (τ + 1)/2`.

Proof outline.
* Pairing. With `w = exp(2π i z₀)`, the terms of index `j` and `-(j+1)` of the series at
  `z₀ + (τ + 1)/2` add up to `(1 - w⁻¹) g_j`, where
  `g_j = exp(π i j) exp(π i j (j+1) τ) Σ_{r=0}^{2j} w^(r-j)` (a finite geometric telescope).
  Hence `θ(z₀ + (τ+1)/2, τ) = (1 - w⁻¹) Σ_{j ≥ 0} g_j` with `g_0 = 1`.
* Estimate. If `|Im z₀| ≤ Im τ / 2` then `‖g_j‖ ≤ (2j+1) ρ^j` with `ρ = exp(-π Im τ)`. On the
  region `4 (Im τ)^2 ≥ 3` this gives `‖Σ g_j - 1‖ < 1`, so the relative series is nonzero,
  uniformly in `N`, `a`, `b`.
* `w ≠ 1` for a balanced representative of a nonzero torsion point.
* The transformation laws under `T` and `S` and quasi-periodicity make the statement
  `SL(2, ℤ)`-invariant; every point is equivalent to one in the standard fundamental domain.

No product formula or description of the zero set is used.
-/

noncomputable section

open Complex ModularGroup
open scoped Modular Real UpperHalfPlane MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelTheta

/-! ### A finite-set tail bound over an arbitrary index type -/

theorem norm_tsum_sub_finset_le' {ι : Type*} {f : ι → ℂ} {M : ι → ℝ} (hf : Summable f)
    (hM : Summable M) (s : Finset ι) (h : ∀ n ∉ s, ‖f n‖ ≤ M n) :
    ‖(∑' n, f n) - ∑ n ∈ s, f n‖ ≤ (∑' n, M n) - ∑ n ∈ s, M n := by
  rw [← hf.sum_add_tsum_compl (s := s), ← hM.sum_add_tsum_compl (s := s),
    add_sub_cancel_left, add_sub_cancel_left]
  have hle : ∀ x : ↥((s : Set ι)ᶜ), ‖f x‖ ≤ M x := fun x => h x (fun hx => x.2 (Finset.mem_coe.mpr hx))
  have hMs : Summable (fun x : ↥((s : Set ι)ᶜ) => M x) := hM.subtype _
  have hfs : Summable (fun x : ↥((s : Set ι)ᶜ) => ‖f x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle hMs
  exact (norm_tsum_le_tsum_norm hfs).trans (hfs.tsum_mono hMs hle)

/-! ### Pairing of the theta series -/

/-- The relative paired term `g_j`. -/
def g (z₀ τ : ℂ) (j : ℕ) : ℂ :=
  cexp (π * I * (j : ℂ)) * cexp (π * I * ((j : ℂ) * (j + 1)) * τ) *
    ∑ r ∈ Finset.range (2 * j + 1), cexp (2 * π * I * z₀) ^ ((r : ℤ) - j)

theorem g_zero (z₀ τ : ℂ) : g z₀ τ 0 = 1 := by
  simp [g]

theorem geom_telescope {w : ℂ} (hw0 : w ≠ 0) (j : ℕ) :
    (1 - w ^ (-1 : ℤ)) * ∑ r ∈ Finset.range (2 * j + 1), w ^ ((r : ℤ) - j) =
      w ^ (j : ℤ) - w ^ (-((j : ℤ) + 1)) := by
  set S := ∑ r ∈ Finset.range (2 * j + 1), w ^ r with hSdef
  have hsum : ∑ r ∈ Finset.range (2 * j + 1), w ^ ((r : ℤ) - j) = w ^ (-(j : ℤ)) * S := by
    rw [hSdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← zpow_natCast, ← zpow_add₀ hw0]
    congr 1; ring
  set P := w ^ (-((j : ℤ) + 1)) with hP
  have hS : S * (w - 1) = w ^ (2 * j + 1) - 1 := geom_sum_mul w (2 * j + 1)
  have e1 : w ^ (j : ℤ) = P * w ^ (2 * j + 1) := by
    rw [hP, ← zpow_natCast, ← zpow_add₀ hw0]; congr 1; push_cast; ring
  have e2 : w ^ (-1 : ℤ) * w ^ (-(j : ℤ)) = P := by
    rw [hP, ← zpow_add₀ hw0]; congr 1; ring
  have e3 : w ^ (-(j : ℤ)) = P * w := by
    rw [hP, ← zpow_add_one₀ hw0]; congr 1; ring
  rw [hsum]
  linear_combination S * e3 - S * e2 - e1 + P * hS

theorem pair_identity (z₀ τ : ℂ) (j : ℕ) :
    jacobiTheta₂_term (j : ℤ) (z₀ + (τ + 1) / 2) τ +
        jacobiTheta₂_term (-((j : ℤ) + 1)) (z₀ + (τ + 1) / 2) τ =
      (1 - cexp (2 * π * I * z₀) ^ (-1 : ℤ)) * g z₀ τ j := by
  set w := cexp (2 * π * I * z₀) with hw
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hwpow : ∀ n : ℤ, cexp (2 * π * I * n * z₀) = w ^ n := fun n => by
    rw [hw, ← Complex.exp_int_mul]; ring_nf
  have hodd : cexp (((-(2 * (j : ℤ) + 1) : ℤ) : ℂ) * (π * I)) = -1 := by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
    exact Odd.neg_one_zpow ⟨-(j : ℤ) - 1, by ring⟩
  have h1 : jacobiTheta₂_term (j : ℤ) (z₀ + (τ + 1) / 2) τ =
      cexp (π * I * (j : ℂ)) * cexp (π * I * ((j : ℂ) * (j + 1)) * τ) * w ^ (j : ℤ) := by
    simp only [jacobiTheta₂_term]
    rw [show 2 * (π : ℂ) * I * ((j : ℤ) : ℂ) * (z₀ + (τ + 1) / 2) + π * I * ((j : ℤ) : ℂ) ^ 2 * τ =
        π * I * (j : ℂ) + π * I * ((j : ℂ) * (j + 1)) * τ + 2 * π * I * ((j : ℤ) : ℂ) * z₀ by
      push_cast; ring]
    rw [Complex.exp_add, Complex.exp_add, hwpow]
  have h2 : jacobiTheta₂_term (-((j : ℤ) + 1)) (z₀ + (τ + 1) / 2) τ =
      -(cexp (π * I * (j : ℂ)) * cexp (π * I * ((j : ℂ) * (j + 1)) * τ) *
        w ^ (-((j : ℤ) + 1))) := by
    simp only [jacobiTheta₂_term]
    rw [show 2 * (π : ℂ) * I * ((-((j : ℤ) + 1) : ℤ) : ℂ) * (z₀ + (τ + 1) / 2) +
        π * I * ((-((j : ℤ) + 1) : ℤ) : ℂ) ^ 2 * τ =
        π * I * (j : ℂ) + ((-(2 * (j : ℤ) + 1) : ℤ) : ℂ) * (π * I) +
          π * I * ((j : ℂ) * (j + 1)) * τ + 2 * π * I * ((-((j : ℤ) + 1) : ℤ) : ℂ) * z₀ by
      push_cast; ring]
    rw [Complex.exp_add, Complex.exp_add, Complex.exp_add, hodd, hwpow]
    ring
  rw [h1, h2, g, ← hw]
  have ht := geom_telescope hw0 j
  linear_combination
    (cexp (π * I * (j : ℂ)) * cexp (π * I * ((j : ℂ) * (j + 1)) * τ)) * ht.symm

/-- The paired form of the theta series: `θ = (1 - w⁻¹) Σ_j g_j`. -/
theorem hasSum_g {z₀ τ : ℂ} (hτ : 0 < τ.im) :
    HasSum (fun j : ℕ => (1 - cexp (2 * π * I * z₀) ^ (-1 : ℤ)) * g z₀ τ j)
      (jacobiTheta₂ (z₀ + (τ + 1) / 2) τ) := by
  have h := (hasSum_jacobiTheta₂_term (z₀ + (τ + 1) / 2) hτ).nat_add_neg_add_one
  refine h.congr_fun ?_
  intro j
  rw [← pair_identity]

/-! ### The estimate of the relative series -/

theorem norm_g_le {z₀ τ : ℂ} (hτ : 0 < τ.im) (hz : |z₀.im| ≤ τ.im / 2) (j : ℕ) :
    ‖g z₀ τ j‖ ≤ (2 * j + 1) * Real.exp (-π * τ.im) ^ j := by
  have hσ : ‖cexp (π * I * (j : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have : (π * I * (j : ℂ)).re = 0 := by simp
    rw [this, Real.exp_zero]
  have hE : ‖cexp (π * I * ((j : ℂ) * (j + 1)) * τ)‖ =
      Real.exp (-π * ((j : ℝ) * (j + 1)) * τ.im) := by
    rw [Complex.norm_exp,
      (by push_cast; ring : (π * I * ((j : ℂ) * (j + 1)) * τ : ℂ) =
        ((π * ((j : ℝ) * (j + 1)) : ℝ) : ℂ) * (τ * I)),
      Complex.re_ofReal_mul, Complex.mul_I_re]
    ring_nf
  have hW : ∀ r ∈ Finset.range (2 * j + 1),
      ‖cexp (2 * π * I * z₀) ^ ((r : ℤ) - j)‖ ≤ Real.exp (π * τ.im * j) := by
    intro r hr
    have hr' : r ≤ 2 * j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    rw [← Complex.exp_int_mul, Complex.norm_exp, Real.exp_le_exp]
    have hre : ((((r : ℤ) - j : ℤ) : ℂ) * (2 * π * I * z₀)).re =
        -(2 * π) * (((r : ℝ) - j) * z₀.im) := by
      simp [Complex.mul_re, Complex.mul_im]
      ring
    rw [hre]
    have habs : |(r : ℝ) - j| ≤ j := by
      rw [abs_le]
      constructor
      · have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        linarith
      · have : (r : ℝ) ≤ 2 * j := by exact_mod_cast hr'
        linarith
    have key : -(((r : ℝ) - j) * z₀.im) ≤ j * (τ.im / 2) := by
      calc -(((r : ℝ) - j) * z₀.im) ≤ |((r : ℝ) - j) * z₀.im| := neg_le_abs _
        _ = |(r : ℝ) - j| * |z₀.im| := abs_mul _ _
        _ ≤ j * (τ.im / 2) := mul_le_mul habs hz (abs_nonneg _) (Nat.cast_nonneg j)
    nlinarith [Real.pi_pos]
  have hsum : ‖∑ r ∈ Finset.range (2 * j + 1), cexp (2 * π * I * z₀) ^ ((r : ℤ) - j)‖ ≤
      (2 * j + 1) * Real.exp (π * τ.im * j) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum hW).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring_nf; exact le_refl _
  rw [g, norm_mul, norm_mul, hσ, hE, one_mul]
  have hjj : (j : ℝ) ≤ (j : ℝ) ^ 2 := by
    have : j ≤ j * j := Nat.le_mul_self j
    have h' : (j : ℝ) ≤ (j : ℝ) * j := by exact_mod_cast this
    nlinarith
  calc Real.exp (-π * ((j : ℝ) * (j + 1)) * τ.im) *
        ‖∑ r ∈ Finset.range (2 * j + 1), cexp (2 * π * I * z₀) ^ ((r : ℤ) - j)‖
      ≤ Real.exp (-π * ((j : ℝ) * (j + 1)) * τ.im) * ((2 * j + 1) * Real.exp (π * τ.im * j)) :=
        mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le
    _ = (2 * j + 1) * Real.exp (-π * τ.im * (j : ℝ) ^ 2) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf
    _ ≤ (2 * j + 1) * Real.exp (-π * τ.im) ^ j := by
        rw [← Real.exp_nat_mul]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Real.exp_le_exp]
        nlinarith [Real.pi_pos, mul_pos Real.pi_pos hτ]

theorem hasSum_majorant {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    HasSum (fun j : ℕ => (2 * (j : ℝ) + 1) * ρ ^ j) (2 * (ρ / (1 - ρ) ^ 2) + (1 - ρ)⁻¹) := by
  have hn : ‖ρ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg h0]
  have hA := (hasSum_coe_mul_geometric_of_norm_lt_one hn).mul_left 2
  have hB := hasSum_geometric_of_lt_one h0 h1
  refine (hA.add hB).congr_fun ?_
  intro j
  ring

/-- **Main estimate.** If `4 (Im τ)^2 ≥ 3`, `|Im z₀| ≤ Im τ / 2` and `exp(2π i z₀) ≠ 1`, then
`θ(z₀ + (τ + 1)/2, τ) ≠ 0`. -/
theorem jacobiTheta₂_shift_ne_zero {z₀ τ : ℂ} (hτ : 0 < τ.im) (h3 : 3 ≤ 4 * τ.im ^ 2)
    (hz : |z₀.im| ≤ τ.im / 2) (hw : cexp (2 * π * I * z₀) ≠ 1) :
    jacobiTheta₂ (z₀ + (τ + 1) / 2) τ ≠ 0 := by
  set w := cexp (2 * π * I * z₀) with hwdef
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hc : (1 - w ^ (-1 : ℤ)) ≠ 0 := by
    rw [zpow_neg_one, sub_ne_zero]
    intro h
    exact hw (by rw [← inv_inv w, ← h, inv_one])
  have hS : HasSum (g z₀ τ) (jacobiTheta₂ (z₀ + (τ + 1) / 2) τ / (1 - w ^ (-1 : ℤ))) := by
    refine ((hasSum_g (z₀ := z₀) hτ).div_const (1 - w ^ (-1 : ℤ))).congr_fun ?_
    intro j
    exact (mul_div_cancel_left₀ _ hc).symm
  set X := Real.pi * τ.im with hX
  have hX5 : 5 / 2 < X := ThetaFive.five_halves_lt_pi_mul_im hτ h3
  set ρ := Real.exp (-π * τ.im) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρu : ρ ≤ Real.exp (-1) * Real.exp (-1) := by
    rw [hρ, ← Real.exp_add, Real.exp_le_exp]; nlinarith
  have hu := ThetaFive.exp_neg_one_lt
  have hu0 : 0 < Real.exp (-1) := Real.exp_pos _
  have hρ1 : ρ < 1 := by nlinarith
  have hM := hasSum_majorant hρ0 hρ1
  have key := norm_tsum_sub_finset_le' hS.summable hM.summable {0} fun j _ => norm_g_le hτ hz j
  rw [hS.tsum_eq, hM.tsum_eq] at key
  simp only [Finset.sum_singleton, g_zero, Nat.cast_zero, mul_zero, zero_add, pow_zero,
    mul_one] at key
  have hlt : 2 * (ρ / (1 - ρ) ^ 2) + (1 - ρ)⁻¹ - 1 < 1 := by
    have h1ρ : 0 < 1 - ρ := by linarith
    have hρ14 : ρ < 0.14 := by nlinarith
    rw [show 2 * (ρ / (1 - ρ) ^ 2) + (1 - ρ)⁻¹ - 1 = (2 * ρ + (1 - ρ) - (1 - ρ) ^ 2) / (1 - ρ) ^ 2 by
      field_simp]
    rw [div_lt_one (by positivity)]
    nlinarith
  intro h0
  rw [h0, zero_div, zero_sub, norm_neg, norm_one] at key
  linarith

/-! ### Level-`N` shifted theta, its symmetries, and the global statement -/

/-- `θ₃` at the level-`N` torsion point `(a τ + b)/N` of the odd theta function. -/
def thetaShift (N : ℕ) (a b : ℤ) (τ : ℂ) : ℂ :=
  jacobiTheta₂ (((a : ℂ) * τ + b) / N + (τ + 1) / 2) τ

/-- Admissible pairs at level `N`. -/
def Good (N : ℕ) (a b : ℤ) : Prop := ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)

variable {N : ℕ}

theorem thetaShift_ne_zero_shift_iff (hN : 0 < N) (a b m n : ℤ) (τ : ℂ) :
    thetaShift N (a + N * m) (b + N * n) τ ≠ 0 ↔ thetaShift N a b τ ≠ 0 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold thetaShift
  have h : (((a + N * m : ℤ) : ℂ) * τ + ((b + N * n : ℤ) : ℂ)) / N + (τ + 1) / 2 =
      ((((a : ℂ) * τ + b) / N + (τ + 1) / 2) + (m : ℂ) * τ) + (n : ℂ) := by
    push_cast; field_simp; ring
  rw [h, ThetaFive.jacobiTheta₂_add_int_left, ThetaFive.ne_zero_add_int_mul_tau_iff]

theorem thetaShift_add_one (hN : 0 < N) (a b : ℤ) (τ : ℂ) :
    thetaShift N a b (τ + 1) = thetaShift N a (a + b) τ := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold thetaShift
  rw [ThetaFive.jacobiTheta₂_add_one_right]
  have h : ((a : ℂ) * (τ + 1) + b) / N + (τ + 1 + 1) / 2 + 1 / 2 =
      (((a : ℂ) * τ + ((a + b : ℤ) : ℂ)) / N + (τ + 1) / 2) + ((1 : ℤ) : ℂ) := by
    push_cast; field_simp; ring
  rw [h, ThetaFive.jacobiTheta₂_add_int_left]

theorem thetaShift_ne_zero_S_iff (hN : 0 < N) (a b : ℤ) {τ : ℂ} (hτ : τ ≠ 0) :
    thetaShift N a b τ ≠ 0 ↔ thetaShift N (-b) a (-1 / τ) ≠ 0 := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hc : (1 : ℂ) / (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    refine one_div_ne_zero ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ h.1
  have hz : (((a : ℂ) * τ + b) / N + (τ + 1) / 2) / τ =
      ((((-b : ℤ) : ℂ) * (-1 / τ) + a) / N + ((-1 / τ) + 1) / 2) + ((-1 : ℤ) : ℂ) * (-1 / τ) := by
    field_simp
    push_cast
    ring
  have key := ThetaFive.ne_zero_add_int_mul_tau_iff
    ((((-b : ℤ) : ℂ) * (-1 / τ) + a) / N + ((-1 / τ) + 1) / 2) (-1 / τ) (-1)
  unfold thetaShift
  rw [jacobiTheta₂_functional_equation, hz]
  constructor
  · intro h
    refine key.mp fun h0 => h ?_
    rw [h0, mul_zero]
  · intro h
    exact mul_ne_zero (mul_ne_zero hc (Complex.exp_ne_zero _)) (key.mpr h)

/-- The statement to be proved at a point. -/
def PropN (N : ℕ) (τ : ℍ) : Prop := ∀ a b : ℤ, Good N a b → thetaShift N a b (τ : ℂ) ≠ 0

theorem good_T {a b : ℤ} (h : Good N a b) (c : ℤ) : Good N a (c * a + b) := by
  rintro ⟨ha, hb⟩
  exact h ⟨ha, by simpa using (Int.dvd_add_right (Dvd.dvd.mul_left ha c)).mp hb⟩

theorem good_S {a b : ℤ} (h : Good N a b) : Good N (-b) a := by
  rintro ⟨hb, ha⟩
  exact h ⟨ha, by simpa using hb⟩

theorem propN_T_iff (hN : 0 < N) (τ : ℍ) : PropN N (T • τ) ↔ PropN N τ := by
  unfold PropN
  rw [ThetaFive.coe_T_smul]
  constructor
  · intro h a b hab
    have := h a (b - a) (by
      have h' := good_T hab (-1)
      rwa [show (-1) * a + b = b - a by ring] at h')
    rwa [thetaShift_add_one hN, show a + (b - a) = b by ring] at this
  · intro h a b hab
    rw [thetaShift_add_one hN]
    exact h a (a + b) (by
      have h' := good_T hab 1
      rwa [one_mul] at h')

theorem propN_S_iff (hN : 0 < N) (τ : ℍ) : PropN N (S • τ) ↔ PropN N τ := by
  unfold PropN
  rw [ThetaFive.coe_S_smul]
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hτ' : -1 / (τ : ℂ) ≠ 0 := div_ne_zero (neg_ne_zero.mpr one_ne_zero) hτ
  have hinv : -1 / (-1 / (τ : ℂ)) = τ := by field_simp
  constructor
  · intro h a b hab
    rw [thetaShift_ne_zero_S_iff hN a b hτ]
    exact h (-b) a (good_S hab)
  · intro h a b hab
    rw [thetaShift_ne_zero_S_iff hN a b hτ', hinv]
    exact h (-b) a (good_S hab)

theorem propN_smul_iff (hN : 0 < N) (γ : SL(2, ℤ)) (τ : ℍ) : PropN N (γ • τ) ↔ PropN N τ := by
  have hg : γ ∈ Subgroup.closure ({S, T} : Set SL(2, ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ
  induction hg using Subgroup.closure_induction generalizing τ with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact propN_S_iff hN τ
    · exact propN_T_iff hN τ
  | one => rw [one_smul]
  | mul x y _ _ hx hy =>
    rw [mul_smul]
    exact (hx (y • τ)).trans (hy τ)
  | inv x _ hx =>
    have h := hx (x⁻¹ • τ)
    rw [smul_inv_smul] at h
    exact h.symm

theorem propN_of_mem_fd (hN : 0 < N) {τ : ℍ} (hτ : τ ∈ 𝒟) : PropN N τ := by
  intro a b hab
  have hy : 0 < (τ : ℂ).im := τ.im_pos
  have h3 : 3 ≤ 4 * (τ : ℂ).im ^ 2 := three_le_four_mul_im_sq_of_mem_fd hτ
  have hNz : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have h2N : (0 : ℤ) < 2 * N := by positivity
  -- balanced representative `a₀ ≡ a (mod N)` with `-N ≤ 2 a₀ < N`
  have hqr := Int.mul_ediv_add_emod (2 * a + N) (2 * N)
  have hr0 := Int.emod_nonneg (2 * a + N) h2N.ne'
  have hr1 := Int.emod_lt_of_pos (2 * a + N) h2N
  generalize (2 * a + (N : ℤ)) / (2 * N) = q at hqr
  generalize (2 * a + (N : ℤ)) % (2 * N) = r at hqr hr0 hr1
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : ℤ, a₀ = a - N * q := ⟨_, rfl⟩
  have hbal1 : -(N : ℤ) ≤ 2 * a₀ := by rw [ha₀]; linarith
  have hbal2 : 2 * a₀ ≤ N := by rw [ha₀]; linarith
  have ea : a₀ + N * q = a := by rw [ha₀]; ring
  rw [show thetaShift N a b (τ : ℂ) = thetaShift N (a₀ + N * q) (b + N * 0) (τ : ℂ) by
    rw [ea, mul_zero, add_zero], thetaShift_ne_zero_shift_iff hN]
  unfold thetaShift
  set z₀ : ℂ := ((a₀ : ℂ) * τ + b) / N with hz₀
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hzim : z₀.im = (a₀ : ℝ) * (τ : ℂ).im / N := by
    have : (N : ℂ) * z₀ = (a₀ : ℂ) * τ + b := by rw [hz₀]; field_simp
    have him := congrArg Complex.im this
    simp at him
    field_simp
    simp only [UpperHalfPlane.coe_im] at him ⊢
    linear_combination him
  refine jacobiTheta₂_shift_ne_zero hy h3 ?_ ?_
  · rw [hzim, abs_div, abs_mul, abs_of_pos hy, abs_of_pos hNr, div_le_iff₀ hNr]
    have h1 : |(a₀ : ℝ)| * 2 ≤ N := by
      have : |a₀| * 2 ≤ N := by
        rcases abs_cases a₀ with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
      exact_mod_cast this
    nlinarith
  · intro hw1
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hw1
    have hz₀n : z₀ = n := by
      have h2 : (2 * π * I : ℂ) ≠ 0 := by
        have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
        exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) I_ne_zero
      have := hn
      rw [mul_comm (2 * π * I : ℂ) z₀] at this
      exact mul_right_cancel₀ h2 this
    have heq : (a₀ : ℂ) * τ + b = (N : ℂ) * n := by
      rw [← hz₀n, hz₀]; field_simp
    have him := congrArg Complex.im heq
    have hre := congrArg Complex.re heq
    simp at him hre
    have ha0 : a₀ = 0 := by
      rcases him with h | h
      · exact_mod_cast h
      · exact absurd h (ne_of_gt τ.im_pos)
    rw [ha0] at hre
    simp at hre
    have hb : b = N * n := by exact_mod_cast hre
    apply hab
    refine ⟨⟨q, ?_⟩, ⟨n, hb⟩⟩
    rw [ha₀] at ha0
    linarith

/-- **Nonvanishing of the odd theta function at nonzero torsion points of every level.** -/
theorem jacobiTheta₂_torsion_ne_zero (N : ℕ) (hN : 0 < N) (τ : ℍ) (a b : ℤ)
    (h : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    jacobiTheta₂ (((a : ℂ) * τ + b) / (N : ℂ) + ((τ : ℂ) + 1) / 2) (τ : ℂ) ≠ 0 := by
  obtain ⟨γ, hγ⟩ := exists_smul_mem_fd τ
  exact (propN_smul_iff hN γ τ).mp (propN_of_mem_fd hN hγ) a b h

/-- The same statement for the shifted point of the level-`N` torsion definitions. -/
theorem jacobiTheta₂_shiftedPoint_ne_zero (N : ℕ) (hN : 0 < N) (τ : ℍ) (a b : ℤ)
    (h : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    jacobiTheta₂ (Torsion.shiftedPoint N a b τ) (τ : ℂ) ≠ 0 :=
  jacobiTheta₂_torsion_ne_zero N hN τ a b h

end ZInQ.Contrib.HeckePrimeRationality.AllLevelTheta
