import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic

/-!
# Two-division multiplication for an entire quasi-theta function

The analytic statements in this file are generic. They do not identify a
particular theta function, nor assert a trace or spanning theorem.
-/

noncomputable section

open Complex Set Filter Function
open scoped Topology Real

namespace QuasiThetaMultiplicationTwo

/-- Division at a simple zero uses the actual complex derivatives. -/
def regularizedQuotient (F G : ℂ → ℂ) (z : ℂ) : ℂ :=
  if G z = 0 then deriv F z / deriv G z else F z / G z

/-- The divided difference of an entire function is entire. -/
lemma differentiable_dslope {F : ℂ → ℂ} (hF : Differentiable ℂ F) (c : ℂ) :
    Differentiable ℂ (dslope F c) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (by simp)).mpr hF.differentiableOn

/-- A simple zero has a punctured neighborhood free of further zeros. -/
lemma eventually_ne_zero_of_simple {G : ℂ → ℂ} {c : ℂ}
    (hG : DifferentiableAt ℂ G c) (hzero : G c = 0) (hsimple : deriv G c ≠ 0) :
    ∀ᶠ z in 𝓝[≠] c, G z ≠ 0 := by
  have h := (continuousAt_dslope_same.mpr hG).eventually_ne
    (by simpa only [dslope_same] using hsimple)
  filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hzc
  have hfac : (z - c) * dslope G c z = G z := by
    simpa only [smul_eq_mul, hzero, sub_zero] using sub_smul_dslope G c z
  rw [← hfac]
  exact mul_ne_zero (sub_ne_zero.mpr hzc) hz

/-- Local analytic cancellation at every simple denominator zero gives an
entire quotient; there is no division by a zero denominator in the proof. -/
theorem differentiable_regularizedQuotient {F G : ℂ → ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hzeros : ∀ c, G c = 0 → F c = 0 ∧ deriv G c ≠ 0) :
    Differentiable ℂ (regularizedQuotient F G) := by
  classical
  intro c
  by_cases hc : G c = 0
  · obtain ⟨hFc, hGc⟩ := hzeros c hc
    have hDF := differentiable_dslope hF c
    have hDG := differentiable_dslope hG c
    have hn : dslope G c c ≠ 0 := by simpa only [dslope_same] using hGc
    have hlocal := (hDG c).continuousAt.eventually_ne hn
    apply ((hDF c).div (hDG c) hn).congr_of_eventuallyEq
    filter_upwards [hlocal] with z hz
    by_cases hzc : z = c
    · subst z
      simp [regularizedQuotient, hc]
    · have hfacG : (z - c) * dslope G c z = G z := by
        simpa only [smul_eq_mul, hc, sub_zero] using sub_smul_dslope G c z
      have hfacF : (z - c) * dslope F c z = F z := by
        simpa only [smul_eq_mul, hFc, sub_zero] using sub_smul_dslope F c z
      have hGz : G z ≠ 0 := by
        rw [← hfacG]
        exact mul_ne_zero (sub_ne_zero.mpr hzc) hz
      simp only [regularizedQuotient, ite_eq_right hGz]
      rw [← hfacF, ← hfacG]
      exact mul_div_mul_left _ _ (sub_ne_zero.mpr hzc)
  · apply ((hF c).div (hG c) hc).congr_of_eventuallyEq
    filter_upwards [(hG c).continuousAt.eventually_ne hc] with z hz
    simp [regularizedQuotient, hz]

/-- The extended quotient satisfies the undivided identity also at zeros. -/
theorem regularizedQuotient_mul {F G : ℂ → ℂ}
    (hzeros : ∀ z, G z = 0 → F z = 0) (z : ℂ) :
    regularizedQuotient F G z * G z = F z := by
  classical
  by_cases hz : G z = 0
  · simp [regularizedQuotient, hz, hzeros z hz]
  · simp [regularizedQuotient, hz]

/-- Common nonzero automorphy becomes a genuine period after analytic
cancellation, including the former singular points. -/
theorem periodic_regularizedQuotient {F G A : ℂ → ℂ} {a : ℂ}
    (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hzeros : ∀ c, G c = 0 → F c = 0 ∧ deriv G c ≠ 0)
    (hA : ∀ z, A z ≠ 0)
    (hFa : ∀ z, F (z + a) = A z * F z)
    (hGa : ∀ z, G (z + a) = A z * G z) :
    Function.Periodic (regularizedQuotient F G) a := by
  classical
  have hQ := differentiable_regularizedQuotient hF hG hzeros
  have hoff (z : ℂ) (hz : G z ≠ 0) :
      regularizedQuotient F G (z + a) = regularizedQuotient F G z := by
    have hza : G (z + a) ≠ 0 := by rw [hGa]; exact mul_ne_zero (hA z) hz
    simp [regularizedQuotient, hFa, hGa, hA z, hz, mul_div_mul_left]
  intro c
  by_cases hc : G c = 0
  · have hn := eventually_ne_zero_of_simple (hG c) hc (hzeros c hc).2
    have hleft : Tendsto (fun z : ℂ => regularizedQuotient F G (z + a))
        (𝓝[≠] c) (𝓝 (regularizedQuotient F G (c + a))) :=
      (hQ.continuous.comp (continuous_id.add continuous_const)).continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    have hright : Tendsto (regularizedQuotient F G) (𝓝[≠] c)
        (𝓝 (regularizedQuotient F G c)) :=
      (hQ c).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (hleft.congr' (hn.mono fun z hz => hoff z hz)) hright
  · exact hoff c hc

/-- A continuous function with periods `1` and an upper-half-plane parameter
is bounded, by reduction to a compact closed parallelogram. -/
theorem bounded_of_continuous_periodic {τ : UpperHalfPlane} {Q : ℂ → ℂ}
    (hQ : Continuous Q) (h1 : Function.Periodic Q 1)
    (hτ : Function.Periodic Q (τ : ℂ)) : Bornology.IsBounded (Set.range Q) := by
  let p : ℝ × ℝ → ℂ := fun t => (t.1 : ℂ) + (t.2 : ℂ) * (τ : ℂ)
  have hp : Continuous p := by fun_prop
  have hK : IsCompact (p '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)) :=
    (isCompact_Icc.prod isCompact_Icc).image hp
  obtain ⟨C, hC⟩ := hK.bddAbove_image hQ.norm.continuousOn
  rw [isBounded_iff_forall_norm_le]
  refine ⟨C, ?_⟩
  rintro _ ⟨z, rfl⟩
  let v : ℝ := z.im / τ.im
  let u : ℝ := z.re - v * τ.re
  let m : ℤ := ⌊u⌋
  let n : ℤ := ⌊v⌋
  let w : ℂ := p (u - m, v - n)
  have hu : u - (m : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (Int.floor_le u), by linarith [Int.lt_floor_add_one u]⟩
  have hv : v - (n : ℝ) ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.mpr (Int.floor_le v), by linarith [Int.lt_floor_add_one v]⟩
  have hw : w ∈ p '' (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    ⟨(u - m, v - n), ⟨hu, hv⟩, rfl⟩
  have hrepr : z = (w + (n : ℂ) * (τ : ℂ)) + (m : ℂ) := by
    apply Complex.ext
    · simp [w, p, u, v, Complex.mul_re]
      ring
    · simp [w, p, v, Complex.mul_im]
      field_simp [τ.im_ne_zero]
      ring
  have hperiod : Q z = Q w := by
    rw [hrepr]
    have hm := h1.int_mul m (w + (n : ℂ) * (τ : ℂ))
    simpa only [mul_one] using hm.trans (hτ.int_mul n w)
  rw [hperiod]
  exact hC ⟨w, hw, rfl⟩

local notation "κ" => ((Real.pi : ℂ) * Complex.I)

/-- The four half-lattice translates, with the two indices independently
ranging over `Fin 2`. -/
def numerator (τ : UpperHalfPlane) (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∏ r : Fin 2, ∏ s : Fin 2,
    H (z + (((r : ℕ) : ℂ) * (τ : ℂ) + ((s : ℕ) : ℂ)) / 2)

/-- The doubled function with its compensating exponential factor. -/
def denominator (H : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (-2 * κ * z) * H (2 * z)

lemma numerator_expanded (τ : UpperHalfPlane) (H : ℂ → ℂ) (z : ℂ) :
    numerator τ H z = (H z * H (z + 1 / 2)) *
      (H (z + (τ : ℂ) / 2) * H (z + ((τ : ℂ) + 1) / 2)) := by
  simp [numerator, Fin.prod_univ_two]

lemma differentiable_numerator {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hH : Differentiable ℂ H) : Differentiable ℂ (numerator τ H) := by
  simp only [funext (numerator_expanded τ H)]
  fun_prop

lemma differentiable_denominator {H : ℂ → ℂ} (hH : Differentiable ℂ H) :
    Differentiable ℂ (denominator H) := by
  unfold denominator
  fun_prop

lemma deriv_add_one {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (h1 : ∀ z, H (z + 1) = -H z) (z : ℂ) :
    deriv H (z + 1) = -deriv H z := by
  have ha : HasDerivAt (fun w : ℂ => H (w + 1)) (deriv H (z + 1)) z := by
    simpa only [Function.comp_def, id_eq, mul_one] using!
      (hH (z + 1)).hasDerivAt.comp z ((hasDerivAt_id z).add_const 1)
  have hb : HasDerivAt (fun w : ℂ => H (w + 1)) (-deriv H z) z :=
    (hH z).hasDerivAt.neg.congr_of_eventuallyEq (Eventually.of_forall h1)
  exact ha.unique hb

lemma deriv_add_tau_of_zero {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hH : Differentiable ℂ H)
    (hτ : ∀ z, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z)
    {z : ℂ} (hz : H z = 0) :
    deriv H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * deriv H z := by
  have ha : HasDerivAt (fun w : ℂ => H (w + (τ : ℂ)))
      (deriv H (z + (τ : ℂ))) z := by
    simpa only [Function.comp_def, id_eq, mul_one] using!
      (hH (z + (τ : ℂ))).hasDerivAt.comp z ((hasDerivAt_id z).add_const (τ : ℂ))
  have he : HasDerivAt (fun w : ℂ => -κ * (τ : ℂ) - 2 * κ * w) (-2 * κ) z := by
    convert! ((hasDerivAt_id z).const_mul (-2 * κ)).const_add (-κ * (τ : ℂ)) using 1
    · funext w; simp only [id_eq]; ring
    · ring
  have hb := (he.cexp.neg.mul (hH z).hasDerivAt).congr_of_eventuallyEq
    (Eventually.of_forall hτ)
  simpa only [hz, mul_zero, zero_add, Pi.neg_apply] using ha.unique hb

/-- A zero together with its nonzero actual complex derivative. -/
def simpleZero (H : ℂ → ℂ) (z : ℂ) : Prop := H z = 0 ∧ deriv H z ≠ 0

lemma periodic_simpleZero_one {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (h1 : ∀ z, H (z + 1) = -H z) : Function.Periodic (simpleZero H) 1 := by
  intro z
  apply propext
  simp [simpleZero, h1, deriv_add_one hH h1]

lemma periodic_simpleZero_tau {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hH : Differentiable ℂ H)
    (hτ : ∀ z, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z) :
    Function.Periodic (simpleZero H) (τ : ℂ) := by
  intro z
  have hmul : -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) ≠ 0 :=
    neg_ne_zero.mpr (Complex.exp_ne_zero _)
  have hziff : H (z + (τ : ℂ)) = 0 ↔ H z = 0 := by
    rw [hτ]
    simp only [mul_eq_zero, hmul, false_or]
  apply propext
  constructor
  · rintro ⟨hz, hd⟩
    have hzz := hziff.mp hz
    refine ⟨hzz, ?_⟩
    rw [deriv_add_tau_of_zero hH hτ hzz] at hd
    exact (mul_ne_zero_iff.mp hd).2
  · rintro ⟨hz, hd⟩
    refine ⟨hziff.mpr hz, ?_⟩
    rw [deriv_add_tau_of_zero hH hτ hz]
    exact mul_ne_zero hmul hd

/-- Simplicity at the origin propagates to all lattice zeros solely by the
two quasi-period relations and complex differentiation. -/
theorem deriv_ne_zero_at_zero {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hH : Differentiable ℂ H)
    (h1 : ∀ z, H (z + 1) = -H z)
    (hτ : ∀ z, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z)
    (hzeros : ∀ z, H z = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * (τ : ℂ))
    (hd0 : deriv H 0 ≠ 0) {z : ℂ} (hz : H z = 0) : deriv H z ≠ 0 := by
  obtain ⟨m, n, rfl⟩ := (hzeros z).mp hz
  have hs0 : simpleZero H 0 := ⟨(hzeros 0).mpr ⟨0, 0, by simp⟩, hd0⟩
  have hp1 := periodic_simpleZero_one hH h1
  have hpτ := periodic_simpleZero_tau hH hτ
  have heq : simpleZero H ((m : ℂ) + (n : ℂ) * (τ : ℂ)) = simpleZero H 0 := by
    calc
      _ = simpleZero H ((n : ℂ) * (τ : ℂ)) := by
        simpa only [mul_one, add_comm] using hp1.int_mul m ((n : ℂ) * (τ : ℂ))
      _ = simpleZero H 0 := by simpa only [zero_add] using hpτ.int_mul n 0
  have hs : simpleZero H ((m : ℂ) + (n : ℂ) * (τ : ℂ)) := by
    rw [heq]
    exact hs0
  exact hs.2

lemma denominator_zero_iff {H : ℂ → ℂ} (z : ℂ) :
    denominator H z = 0 ↔ H (2 * z) = 0 := by
  simp [denominator, Complex.exp_ne_zero]

/-- All zeros of the compensated doubled function are simple. -/
theorem denominator_deriv_ne_zero_at_zero {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hH : Differentiable ℂ H)
    (h1 : ∀ z, H (z + 1) = -H z)
    (hτ : ∀ z, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z)
    (hzeros : ∀ z, H z = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * (τ : ℂ))
    (hd0 : deriv H 0 ≠ 0) {z : ℂ} (hz : denominator H z = 0) :
    deriv (denominator H) z ≠ 0 := by
  have hHz := (denominator_zero_iff z).mp hz
  have hdH := deriv_ne_zero_at_zero hH h1 hτ hzeros hd0 hHz
  have hlin : HasDerivAt (fun w : ℂ => 2 * w) 2 z := by
    simpa using! ((hasDerivAt_id z).const_mul (2 : ℂ))
  have hscale : HasDerivAt (fun w : ℂ => H (2 * w)) (deriv H (2 * z) * 2) z := by
    simpa only [Function.comp_def] using! (hH (2 * z)).hasDerivAt.comp z hlin
  have he : HasDerivAt (fun w : ℂ => Complex.exp (-2 * κ * w))
      (Complex.exp (-2 * κ * z) * (-2 * κ)) z := by
    simpa using! ((hasDerivAt_id z).const_mul (-2 * κ)).cexp
  have hd : deriv (denominator H) z =
      (Complex.exp (-2 * κ * z) * (-2 * κ)) * H (2 * z) +
        Complex.exp (-2 * κ * z) * (deriv H (2 * z) * 2) := by
    simpa only [denominator, Pi.mul_apply] using! (he.mul hscale).deriv
  rw [hd, hHz, mul_zero, zero_add]
  exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero hdH (by norm_num))

lemma numerator_zero_iff_factor (τ : UpperHalfPlane) (H : ℂ → ℂ) (z : ℂ) :
    numerator τ H z = 0 ↔ ∃ r s : Fin 2,
      H (z + (((r : ℕ) : ℂ) * (τ : ℂ) + ((s : ℕ) : ℂ)) / 2) = 0 := by
  simp only [numerator, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]

/-- The four translates vanish exactly on the doubled lattice, without any
assumption of a multiplication formula. -/
theorem numerator_zero_iff_denominator_zero {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hzeros : ∀ z, H z = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * (τ : ℂ))
    (z : ℂ) : numerator τ H z = 0 ↔ denominator H z = 0 := by
  rw [numerator_zero_iff_factor, denominator_zero_iff, hzeros]
  constructor
  · rintro ⟨r, s, hrs⟩
    obtain ⟨m, n, hmn⟩ := (hzeros _).mp hrs
    refine ⟨2 * m - (s : ℕ), 2 * n - (r : ℕ), ?_⟩
    push_cast
    linear_combination (2 : ℂ) * hmn
  · rintro ⟨m, n, hmn⟩
    have hm : m / 2 * 2 + m % 2 = m := Int.ediv_mul_add_emod m 2
    have hn : n / 2 * 2 + n % 2 = n := Int.ediv_mul_add_emod n 2
    let r : Fin 2 := ⟨(n % 2).toNat, by omega⟩
    let s : Fin 2 := ⟨(m % 2).toNat, by omega⟩
    have hr : ((r : ℕ) : ℤ) = n % 2 := by dsimp [r]; omega
    have hs : ((s : ℕ) : ℤ) = m % 2 := by dsimp [s]; omega
    have hrc : ((r : ℕ) : ℂ) = ((n % 2 : ℤ) : ℂ) := by exact_mod_cast hr
    have hsc : ((s : ℕ) : ℂ) = ((m % 2 : ℤ) : ℂ) := by exact_mod_cast hs
    have hmc : (m / 2 : ℤ) * (2 : ℂ) + (m % 2 : ℤ) = (m : ℂ) := by
      exact_mod_cast hm
    have hnc : (n / 2 : ℤ) * (2 : ℂ) + (n % 2 : ℤ) = (n : ℂ) := by
      exact_mod_cast hn
    refine ⟨r, s, (hzeros _).mpr ⟨m / 2 + m % 2, n / 2 + n % 2, ?_⟩⟩
    push_cast
    rw [hrc, hsc]
    linear_combination (1 / 2 : ℂ) * hmn -
      (1 / 2 : ℂ) * hmc - ((τ : ℂ) / 2) * hnc

/-- Integer multiples of `2πi` do not affect the exponential. -/
lemma exp_add_int_two_pi_I (w : ℂ) (n : ℤ) :
    Complex.exp (w + (n : ℂ) * (2 * κ)) = Complex.exp w := by
  rw [Complex.exp_add]
  have hn : Complex.exp ((n : ℂ) * (2 * κ)) = 1 := by
    convert Complex.exp_int_mul_two_pi_mul_I n using 2
    ring
  rw [hn, mul_one]

lemma exp_neg_two_pi_I : Complex.exp (-2 * κ) = 1 := by
  convert Complex.exp_int_mul_two_pi_mul_I (-1) using 2
  push_cast
  ring

lemma numerator_add_one {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (h1 : ∀ z, H (z + 1) = -H z) (z : ℂ) :
    numerator τ H (z + 1) = numerator τ H z := by
  rw [numerator_expanded, numerator_expanded]
  have ha (a : ℂ) : H ((z + 1) + a) = -H (z + a) := by
    rw [show (z + 1) + a = (z + a) + 1 by ring, h1]
  rw [h1, ha (1 / 2), ha ((τ : ℂ) / 2), ha (((τ : ℂ) + 1) / 2)]
  ring

lemma denominator_add_one {H : ℂ → ℂ}
    (h1 : ∀ z, H (z + 1) = -H z) (z : ℂ) :
    denominator H (z + 1) = denominator H z := by
  have h2 : H (2 * (z + 1)) = H (2 * z) := by
    rw [show 2 * (z + 1) = (2 * z + 1) + 1 by ring, h1, h1, neg_neg]
  simp only [denominator, h2]
  rw [show -2 * κ * (z + 1) = (-2 * κ * z) + -2 * κ by ring,
    Complex.exp_add, exp_neg_two_pi_I, mul_one]

/-- The shared multiplier for translation by `τ`. -/
def doubledMultiplier (τ : UpperHalfPlane) (z : ℂ) : ℂ :=
  Complex.exp (-6 * κ * (τ : ℂ) - 8 * κ * z)

lemma numerator_add_tau {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hτ : ∀ z, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z) (z : ℂ) :
    numerator τ H (z + (τ : ℂ)) = doubledMultiplier τ z * numerator τ H z := by
  have ha (a : ℂ) : H ((z + (τ : ℂ)) + a) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * (z + a)) * H (z + a) := by
    rw [show (z + (τ : ℂ)) + a = (z + a) + (τ : ℂ) by ring, hτ]
  simp only [numerator_expanded]
  rw [hτ, ha (1 / 2), ha ((τ : ℂ) / 2), ha (((τ : ℂ) + 1) / 2)]
  have he : Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) *
      Complex.exp (-κ * (τ : ℂ) - 2 * κ * (z + 1 / 2)) *
      Complex.exp (-κ * (τ : ℂ) - 2 * κ * (z + (τ : ℂ) / 2)) *
      Complex.exp (-κ * (τ : ℂ) - 2 * κ * (z + ((τ : ℂ) + 1) / 2)) =
        doubledMultiplier τ z := by
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    unfold doubledMultiplier
    rw [show (-κ * (τ : ℂ) - 2 * κ * z) +
      (-κ * (τ : ℂ) - 2 * κ * (z + 1 / 2)) +
      (-κ * (τ : ℂ) - 2 * κ * (z + (τ : ℂ) / 2)) +
      (-κ * (τ : ℂ) - 2 * κ * (z + ((τ : ℂ) + 1) / 2)) =
        (-6 * κ * (τ : ℂ) - 8 * κ * z) + (-1 : ℂ) * (2 * κ) by ring]
    simpa only [Int.cast_neg, Int.cast_one] using exp_add_int_two_pi_I
      (-6 * κ * (τ : ℂ) - 8 * κ * z) (-1)
  calc
    _ = (Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) *
      Complex.exp (-κ * (τ : ℂ) - 2 * κ * (z + 1 / 2)) *
      Complex.exp (-κ * (τ : ℂ) - 2 * κ * (z + (τ : ℂ) / 2)) *
      Complex.exp (-κ * (τ : ℂ) - 2 * κ * (z + ((τ : ℂ) + 1) / 2))) *
        ((H z * H (z + 1 / 2)) * (H (z + (τ : ℂ) / 2) *
          H (z + ((τ : ℂ) + 1) / 2))) := by ring
    _ = _ := by rw [he]

lemma denominator_add_tau {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hτ : ∀ z, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z) (z : ℂ) :
    denominator H (z + (τ : ℂ)) = doubledMultiplier τ z * denominator H z := by
  have h2 : H (2 * (z + (τ : ℂ))) =
      (Complex.exp (-κ * (τ : ℂ) - 2 * κ * (2 * z + (τ : ℂ))) *
        Complex.exp (-κ * (τ : ℂ) - 2 * κ * (2 * z))) * H (2 * z) := by
    rw [show 2 * (z + (τ : ℂ)) = (2 * z + (τ : ℂ)) + (τ : ℂ) by ring, hτ, hτ]
    ring
  simp only [denominator, h2]
  have he : Complex.exp (-2 * κ * (z + (τ : ℂ))) *
      Complex.exp (-κ * (τ : ℂ) - 2 * κ * (2 * z + (τ : ℂ))) *
      Complex.exp (-κ * (τ : ℂ) - 2 * κ * (2 * z)) =
      doubledMultiplier τ z * Complex.exp (-2 * κ * z) := by
    unfold doubledMultiplier
    rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  calc
    _ = (Complex.exp (-2 * κ * (z + (τ : ℂ))) *
      Complex.exp (-κ * (τ : ℂ) - 2 * κ * (2 * z + (τ : ℂ))) *
      Complex.exp (-κ * (τ : ℂ) - 2 * κ * (2 * z))) * H (2 * z) := by ring
    _ = _ := by rw [he]; ring

/-- A real half-integer is not a lattice point when `Im τ > 0`. -/
lemma half_ne_zero {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hzeros : ∀ z, H z = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * (τ : ℂ)) :
    H (1 / 2) ≠ 0 := by
  intro hz
  obtain ⟨m, n, hmn⟩ := (hzeros (1 / 2)).mp hz
  have hi := congr_arg Complex.im hmn
  norm_num [Complex.mul_im] at hi
  have hn : n = 0 := hi.resolve_right τ.im_ne_zero
  subst n
  have hr := congr_arg Complex.re hmn
  norm_num at hr
  have hmR : (2 : ℝ) * (m : ℝ) = 1 := by linarith
  have hm : (2 : ℤ) * m = 1 := by exact_mod_cast hmR
  omega

lemma denominator_quarter_ne_zero {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hzeros : ∀ z, H z = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * (τ : ℂ)) :
    denominator H (1 / 4) ≠ 0 := by
  intro hz
  have hh := (denominator_zero_iff (H := H) (1 / 4)).mp hz
  norm_num at hh
  exact half_ne_zero hzeros hh

/-- The explicit extended quotient of the four translates by the doubled
function is entire and has both lattice periods. -/
theorem quotient_entire_periodic {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hH : Differentiable ℂ H)
    (h1 : ∀ z, H (z + 1) = -H z)
    (hτ : ∀ z, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z)
    (hzeros : ∀ z, H z = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * (τ : ℂ))
    (hd0 : deriv H 0 ≠ 0) :
    Differentiable ℂ (regularizedQuotient (numerator τ H) (denominator H)) ∧
      Function.Periodic (regularizedQuotient (numerator τ H) (denominator H)) 1 ∧
      Function.Periodic (regularizedQuotient (numerator τ H) (denominator H)) (τ : ℂ) := by
  have hP := differentiable_numerator (τ := τ) hH
  have hE := differentiable_denominator hH
  have hdivisor : ∀ c, denominator H c = 0 →
      numerator τ H c = 0 ∧ deriv (denominator H) c ≠ 0 := by
    intro c hc
    exact ⟨(numerator_zero_iff_denominator_zero hzeros c).mpr hc,
      denominator_deriv_ne_zero_at_zero hH h1 hτ hzeros hd0 hc⟩
  refine ⟨differentiable_regularizedQuotient hP hE hdivisor, ?_, ?_⟩
  · exact periodic_regularizedQuotient (A := fun _ => 1) hP hE hdivisor
      (by simp) (by simpa using numerator_add_one (τ := τ) h1)
      (by simpa using denominator_add_one h1)
  · exact periodic_regularizedQuotient (A := doubledMultiplier τ) hP hE hdivisor
      (fun z => Complex.exp_ne_zero _) (numerator_add_tau hτ) (denominator_add_tau hτ)

/-- Two-division multiplication derived from explicit, independent analytic
hypotheses. No multiplication identity, quotient constancy, basis, trace,
or spanning statement is among the premises. -/
theorem multiplication_two {τ : UpperHalfPlane} {H : ℂ → ℂ}
    (hH : Differentiable ℂ H)
    (h1 : ∀ z, H (z + 1) = -H z)
    (hτ : ∀ z, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z)
    (hzeros : ∀ z, H z = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * (τ : ℂ))
    (hd0 : deriv H 0 ≠ 0) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ z : ℂ,
      (∏ r : Fin 2, ∏ s : Fin 2,
        H (z + (((r : ℕ) : ℂ) * (τ : ℂ) + ((s : ℕ) : ℂ)) / 2)) =
          C * Complex.exp (-2 * κ * z) * H (2 * z) := by
  obtain ⟨hQ, hQ1, hQτ⟩ := quotient_entire_periodic hH h1 hτ hzeros hd0
  have hb := bounded_of_continuous_periodic hQ.continuous hQ1 hQτ
  let C : ℂ := regularizedQuotient (numerator τ H) (denominator H) (1 / 4)
  have hc (z : ℂ) : regularizedQuotient (numerator τ H) (denominator H) z = C :=
    hQ.apply_eq_apply_of_bounded hb z (1 / 4)
  have hE4 : denominator H (1 / 4) ≠ 0 := denominator_quarter_ne_zero hzeros
  have hP4 : numerator τ H (1 / 4) ≠ 0 := by
    intro hp
    exact hE4 ((numerator_zero_iff_denominator_zero hzeros (1 / 4)).mp hp)
  have hC : C ≠ 0 := by
    dsimp [C, regularizedQuotient]
    rw [ite_eq_right hE4]
    exact div_ne_zero hP4 hE4
  refine ⟨C, hC, ?_⟩
  intro z
  have hidentity := regularizedQuotient_mul
    (fun w hw => (numerator_zero_iff_denominator_zero hzeros w).mpr hw) z
  rw [hc z] at hidentity
  change numerator τ H z = C * Complex.exp (-2 * κ * z) * H (2 * z)
  simpa only [denominator, mul_assoc] using hidentity.symm

/-- The same conclusion with every analytic premise and exponential phase
written explicitly, for use as a generic interface. Oddness is not needed
as an additional premise. -/
theorem multiplication_two_explicit (τ : UpperHalfPlane) (H : ℂ → ℂ)
    (hEntire : Differentiable ℂ H)
    (hOne : ∀ z : ℂ, H (z + 1) = -H z)
    (hTau : ∀ z : ℂ, H (z + (τ : ℂ)) =
      -Complex.exp (-(Real.pi : ℂ) * Complex.I * (τ : ℂ) -
        2 * (Real.pi : ℂ) * Complex.I * z) * H z)
    (hZeroSet : ∀ z : ℂ, H z = 0 ↔
      ∃ m n : ℤ, z = (m : ℂ) + (n : ℂ) * (τ : ℂ))
    (hDerivative : deriv H 0 ≠ 0) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ z : ℂ,
      (∏ r : Fin 2, ∏ s : Fin 2,
        H (z + ((r : ℂ) * (τ : ℂ) + (s : ℂ)) / 2)) =
          C * Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * z) * H (2 * z) := by
  have hTau' : ∀ z : ℂ, H (z + (τ : ℂ)) =
      -Complex.exp (-κ * (τ : ℂ) - 2 * κ * z) * H z := by
    intro z
    simpa only [mul_assoc, neg_mul] using hTau z
  obtain ⟨C, hC, hformula⟩ := multiplication_two hEntire hOne hTau' hZeroSet hDerivative
  refine ⟨C, hC, ?_⟩
  intro z
  simpa only [mul_assoc] using hformula z

end QuasiThetaMultiplicationTwo
