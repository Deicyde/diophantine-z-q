import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-! The ordinary theta function does not vanish on the upper half plane.
The proof uses the duplication identity for the alternating series and decay
at infinity (provenance (c)). -/

noncomputable section

namespace ZInQ.Manuscript.RC.HalfIntegral

open Complex Filter
open scoped Topology Real

private def phase (n : ℤ) : ℂ := if n % 2 = 0 then 1 else -1

private theorem exp_int_sq_pi (n : ℤ) : exp (π * I * (n : ℂ) ^ 2) = phase n := by
  rw [show (π : ℂ) * I * (n : ℂ) ^ 2 = ((n ^ 2 : ℤ) : ℂ) * (π * I) by push_cast; ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I, neg_one_zpow_eq_ite]
  have h : Even (n ^ 2) ↔ n % 2 = 0 := by rw [pow_two, Int.even_mul, or_self, Int.even_iff]
  simp [phase, h]

private def Lattice : Set (ℤ × ℤ) := {p | (p.1 + p.2) % 2 = 0}

private def latticeEquiv : (ℤ × ℤ) ≃ Lattice where
  toFun p := ⟨(p.1 + p.2, p.1 - p.2), by
    change (p.1 + p.2 + (p.1 - p.2)) % 2 = 0
    omega⟩
  invFun p := ((p.1.1 + p.1.2) / 2, (p.1.1 - p.1.2) / 2)
  left_inv p := Prod.ext (by dsimp; omega) (by dsimp; omega)
  right_inv p := by
    have hp : (p.1.1 + p.1.2) % 2 = 0 := p.2
    apply Subtype.ext
    exact Prod.ext (by dsimp; omega) (by dsimp; omega)

private theorem summable_theta_norm {τ : ℂ} (hτ : 0 < τ.im) :
    Summable fun n : ℤ ↦ ‖exp (π * I * (n : ℂ) ^ 2 * τ)‖ := by
  rw [summable_norm_iff]
  simpa only [jacobiTheta₂_term, mul_zero, zero_add] using
    (summable_jacobiTheta₂_term_iff 0 τ).mpr hτ

/-- The product of the ordinary and alternating series is the square of the
alternating series at twice the argument. -/
theorem jacobiTheta_mul_add_one {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ * jacobiTheta (τ + 1) = jacobiTheta (2 * τ + 1) ^ 2 := by
  classical
  have hτ₁ : 0 < (τ + 1).im := by simpa only [Complex.add_im, Complex.one_im, add_zero] using hτ
  have hτ₂ : 0 < (2 * τ + 1).im := by
    have : (2 * τ + 1).im = 2 * τ.im := by simp [Complex.mul_im]
    rw [this]
    positivity
  let F (p : ℤ × ℤ) := exp (π * I * (p.1 : ℂ)^2 * τ) * exp (π * I * (p.2 : ℂ)^2 * (τ + 1))
  let G (p : ℤ × ℤ) := exp (π * I * (p.1 : ℂ)^2 * (2 * τ + 1)) *
    exp (π * I * (p.2 : ℂ)^2 * (2 * τ + 1))
  have hF : Summable F := by
    exact summable_mul_of_summable_norm
      (f := fun n : ℤ ↦ exp (π * I * (n : ℂ)^2 * τ))
      (g := fun n : ℤ ↦ exp (π * I * (n : ℂ)^2 * (τ + 1)))
      (summable_theta_norm hτ) (summable_theta_norm hτ₁)
  have hswap := (Equiv.prodComm ℤ ℤ).summable_iff.mpr (show Summable F from hF)
  have hsym : ∀ p, F p + F p.swap = Lattice.indicator (fun x ↦ 2 * F x) p := by
    intro p
    have hphase (n : ℤ) :
        exp (π * I * (n : ℂ)^2 * (τ + 1)) = exp (π * I * (n : ℂ)^2 * τ) * phase n := by
      rw [mul_add, mul_one, Complex.exp_add, exp_int_sq_pi]
    by_cases hp : p ∈ Lattice
    · have hp' : (p.1 + p.2) % 2 = 0 := hp
      have he : (p.1 % 2 = 0) = (p.2 % 2 = 0) := propext (by omega)
      simp only [Set.indicator_of_mem hp, F, Prod.fst_swap, Prod.snd_swap, hphase, phase, he]
      ring
    · have hp' : (p.1 + p.2) % 2 ≠ 0 := hp
      simp only [Set.indicator_of_notMem hp, F, Prod.fst_swap, Prod.snd_swap, hphase, phase]
      split_ifs <;> first | omega | ring
  have hFG (p : ℤ × ℤ) : F (latticeEquiv p) = G p := by
    dsimp [F, G, latticeEquiv]
    rw [← Complex.exp_add, ← Complex.exp_add]
    have hE := Complex.exp_int_mul_two_pi_mul_I (-(p.1 * p.2))
    calc
      _ = exp (π * I * (p.1 : ℂ)^2 * (2 * τ + 1) + π * I * (p.2 : ℂ)^2 * (2 * τ + 1) +
          ((-(p.1 * p.2) : ℤ) : ℂ) * (2 * π * I)) := by
        congr 1
        push_cast
        ring
      _ = _ := by rw [Complex.exp_add, hE, mul_one]
  rw [jacobiTheta, jacobiTheta, jacobiTheta, pow_two,
    tsum_mul_tsum_of_summable_norm (summable_theta_norm hτ) (summable_theta_norm hτ₁),
    tsum_mul_tsum_of_summable_norm (summable_theta_norm hτ₂) (summable_theta_norm hτ₂)]
  change (∑' p, F p) = ∑' p, G p
  have h : 2 * (∑' p, F p) = 2 * (∑' p, G p) := calc
    _ = ∑' p, (F p + F p.swap) := by
      have hs := Summable.tsum_add (f := F) (g := fun p : ℤ × ℤ ↦ F p.swap) hF hswap
      have he : (∑' p : ℤ × ℤ, F p.swap) = (∑' p, F p) := (Equiv.prodComm ℤ ℤ).tsum_eq F
      rw [hs, he]
      ring
    _ = ∑' p, Lattice.indicator (fun p ↦ 2 * F p) p := tsum_congr hsym
    _ = ∑' p : Lattice, 2 * F p := (tsum_subtype Lattice (fun p ↦ 2 * F p)).symm
    _ = _ := by rw [← latticeEquiv.tsum_eq (fun p ↦ 2 * F p)]; simp_rw [hFG, tsum_mul_left]
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h

/-- Jacobi's theta series has no zeros in the upper half plane. -/
theorem jacobiTheta_ne_zero_of_im_pos {τ : ℂ} (hτ : 0 < τ.im) : jacobiTheta τ ≠ 0 := by
  intro hz
  have hIm (n : ℕ) : (((2 : ℂ) ^ n) * τ).im = (2 : ℝ) ^ n * τ.im := calc
    _ = ((ofReal ((2 : ℝ) ^ n)) * τ).im := by push_cast; rfl
    _ = _ := Complex.im_ofReal_mul _ _
  have hzero (n : ℕ) : jacobiTheta ((2 : ℂ) ^ (n + 1) * τ + 1) = 0 := by
    induction n with
    | zero =>
      have h := jacobiTheta_mul_add_one hτ
      rw [hz, zero_mul] at h
      simpa using ((pow_eq_zero_iff two_ne_zero).mp h.symm)
    | succ n ih =>
      have hi : 0 < (((2 : ℂ) ^ (n + 1)) * τ).im := by
        rw [hIm]
        positivity
      have h := jacobiTheta_mul_add_one hi
      rw [ih, mul_zero] at h
      have hh := (pow_eq_zero_iff two_ne_zero).mp h.symm
      simpa only [pow_succ' (2 : ℂ) (n + 1), mul_assoc] using hh
  have hsm : Tendsto (fun n : ℕ ↦ (2 : ℂ) ^ (n + 1) * τ + 1) atTop (comap im atTop) := by
    rw [tendsto_comap_iff]
    have h (n : ℕ) : (((2 : ℂ) ^ (n + 1) * τ + 1)).im = (2 : ℝ) ^ n * (2 * τ.im) := by
      rw [Complex.add_im, Complex.one_im, add_zero, hIm, pow_succ, mul_assoc]
    simpa only [Function.comp_def, h] using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const (by positivity)
  have hdec : Tendsto (fun n : ℕ ↦ Real.exp (-π * (((2 : ℂ) ^ (n + 1) * τ + 1)).im))
      atTop (𝓝 0) := Real.tendsto_exp_atBot.comp
    ((tendsto_comap_iff.mp hsm).const_mul_atTop_of_neg (by linarith [Real.pi_pos]))
  have hh := (isBigO_at_im_infty_jacobiTheta_sub_one.comp_tendsto hsm).trans_tendsto hdec
  simp only [Function.comp_def, hzero, zero_sub] at hh
  exact (by norm_num : (-1 : ℂ) ≠ 0) (tendsto_nhds_unique tendsto_const_nhds hh)

#print axioms exp_int_sq_pi
#print axioms summable_theta_norm
#print axioms jacobiTheta_mul_add_one
#print axioms jacobiTheta_ne_zero_of_im_pos

end ZInQ.Manuscript.RC.HalfIntegral
