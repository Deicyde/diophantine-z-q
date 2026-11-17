import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaAdditionLocal

/-!
# Global addition analysis of the actual completed theta function

The local pole cancellation is supplied by an explicit divided difference of the
actual regular part. This file transports it by the two theta periods and oddness.
No Weierstrass identification or addition theorem is a premise.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Function
open scoped Topology Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.ThetaAddition

open CompletedTheta
local notation "κ" => ((Real.pi : ℂ) * Complex.I)

private def phase (τ : ℍ) (z : ℂ) : ℂ := -cexp (-κ * (τ : ℂ) - 2 * κ * z)

private theorem phase_ne_zero (τ : ℍ) (z : ℂ) : phase τ z ≠ 0 :=
  neg_ne_zero.mpr (Complex.exp_ne_zero _)

private theorem H_shift_tau (τ : ℍ) (z : ℂ) :
    H τ (z + τ) = phase τ z * H τ z := by
  simpa only [phase, neg_mul, mul_assoc] using H_add_tau τ z

theorem deriv_H_even (τ : ℍ) (z : ℂ) : deriv (H τ) (-z) = deriv (H τ) z := by
  have ha : HasDerivAt (fun w : ℂ => H τ (-w)) (-deriv (H τ) (-z)) z := by
    simpa only [zero_sub] using HasDerivAt.comp_const_sub (0 : ℂ) z
      (by simpa only [zero_sub] using ((differentiable_H τ) (-z)).hasDerivAt)
  have hb : HasDerivAt (fun w : ℂ => H τ (-w)) (-deriv (H τ) z) z :=
    ((differentiable_H τ) z).hasDerivAt.neg.congr_of_eventuallyEq
      (Eventually.of_forall (H_neg τ))
  have he := ha.unique hb
  linear_combination -he

theorem L_neg (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) : L τ (-z) = -L τ z := by
  unfold L
  rw [deriv_H_even, H_neg]
  field_simp

theorem deriv_L_even (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) :
    deriv (L τ) (-z) = deriv (L τ) z := by
  have hn : H τ (-z) ≠ 0 := by rw [H_neg]; exact neg_ne_zero.mpr hz
  have ha : HasDerivAt (fun w : ℂ => L τ (-w)) (-deriv (L τ) (-z)) z := by
    simpa only [zero_sub] using HasDerivAt.comp_const_sub (0 : ℂ) z
      (by simpa only [zero_sub] using (differentiableAt_L τ hn).hasDerivAt)
  have heq : (fun w : ℂ => L τ (-w)) =ᶠ[𝓝 z] fun w => -L τ w := by
    filter_upwards [((differentiable_H τ) z).continuousAt.eventually_ne hz] with w hw
    exact L_neg τ hw
  have hb := (differentiableAt_L τ hz).hasDerivAt.neg.congr_of_eventuallyEq heq
  have he := ha.unique hb
  linear_combination -he

private theorem deriv_H_shift_tau (τ : ℍ) (z : ℂ) :
    deriv (H τ) (z + τ) = phase τ z * (deriv (H τ) z - 2 * κ * H τ z) := by
  have hi : HasDerivAt (fun w : ℂ => -κ * (τ : ℂ) - 2 * κ * w) (-2 * κ) z := by
    convert ((hasDerivAt_id z).const_mul (-2 * κ)).const_add (-κ * (τ : ℂ)) using 1
    · funext w
      simp only [id_eq]
      ring
    · simp only [mul_one]
  have he : HasDerivAt (phase τ) (phase τ z * (-2 * κ)) z := by
    have he0 := hi.cexp.neg
    change HasDerivAt (phase τ)
      (-(cexp (-κ * (τ : ℂ) - 2 * κ * z) * (-2 * κ))) z at he0
    convert he0 using 1
    unfold phase
    ring
  have ha := HasDerivAt.comp_add_const z (τ : ℂ)
    ((differentiable_H τ) (z + τ)).hasDerivAt
  have hb := (he.mul ((differentiable_H τ) z).hasDerivAt).congr_of_eventuallyEq
    (Eventually.of_forall (H_shift_tau τ))
  calc
    deriv (H τ) (z + τ) = (phase τ z * (-2 * κ)) * H τ z + phase τ z * deriv (H τ) z :=
      ha.unique hb
    _ = phase τ z * (deriv (H τ) z - 2 * κ * H τ z) := by ring

theorem L_add_one (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) : L τ (z + 1) = L τ z := by
  unfold L
  rw [QuasiThetaMultiplicationTwo.deriv_add_one (differentiable_H τ) (H_add_one τ), H_add_one]
  field_simp

theorem L_add_tau (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) :
    L τ (z + τ) = L τ z - 2 * κ := by
  unfold L
  rw [deriv_H_shift_tau, H_shift_tau]
  have he := phase_ne_zero τ z
  field_simp

private theorem deriv_L_shift (τ : ℍ) (p b : ℂ) {z : ℂ}
    (hz : H τ z ≠ 0) (hzp : H τ (z + p) ≠ 0)
    (hshift : ∀ w, H τ w ≠ 0 → L τ (w + p) = L τ w + b) :
    deriv (L τ) (z + p) = deriv (L τ) z := by
  have ha := HasDerivAt.comp_add_const z p (differentiableAt_L τ hzp).hasDerivAt
  have he : (fun w : ℂ => L τ (w + p)) =ᶠ[𝓝 z] fun w => L τ w + b := by
    filter_upwards [((differentiable_H τ) z).continuousAt.eventually_ne hz] with w hw
    exact hshift w hw
  have hb := ((differentiableAt_L τ hz).hasDerivAt.add_const b).congr_of_eventuallyEq he
  exact ha.unique hb

theorem deriv_L_add_one (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) :
    deriv (L τ) (z + 1) = deriv (L τ) z := by
  have hn : H τ (z + 1) ≠ 0 := by rw [H_add_one]; exact neg_ne_zero.mpr hz
  exact deriv_L_shift τ 1 0 hz hn (fun w hw => by rw [L_add_one τ hw, add_zero])

theorem deriv_L_add_tau (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) :
    deriv (L τ) (z + τ) = deriv (L τ) z := by
  have hn : H τ (z + τ) ≠ 0 := by
    rw [H_shift_tau]
    exact mul_ne_zero (phase_ne_zero τ z) hz
  exact deriv_L_shift τ (τ : ℂ) (-2 * κ) hz hn
    (fun w hw => by simpa only [sub_eq_add_neg, neg_mul] using L_add_tau τ hw)

/-- Candidate extension at the two zero cosets. Its analyticity is proved below
from the actual local divided-difference extension. -/
def regularized (τ : ℍ) (v z : ℂ) : ℂ :=
  if H τ z = 0 ∨ H τ (z + v) = 0 then 3 * c τ else expression τ v z

theorem regularized_zero (τ : ℍ) (v : ℂ) : regularized τ v 0 = 3 * c τ := by
  simp only [regularized, H_zero, true_or, if_true]

private theorem regularized_off (τ : ℍ) {v z : ℂ}
    (hz : H τ z ≠ 0) (hzv : H τ (z + v) ≠ 0) :
    regularized τ v z = expression τ v z := by
  simp only [regularized, hz, hzv, false_or, if_false]

theorem regularized_origin_germ (τ : ℍ) {v : ℂ} (hv : H τ v ≠ 0) :
    regularized τ v =ᶠ[𝓝 (0 : ℂ)] originExtension τ v := by
  have he := (origin_local_extension τ hv).2.2
  have hn := eventually_nhdsWithin_iff.mp he
  filter_upwards [hn] with z hz
  by_cases hz0 : z = 0
  · subst z
    rw [regularized_zero, originExtension_zero τ hv]
  · have hx := hz hz0
    exact (regularized_off τ hx.1 hx.2.1).trans hx.2.2

theorem differentiableAt_regularized_zero (τ : ℍ) {v : ℂ} (hv : H τ v ≠ 0) :
    DifferentiableAt ℂ (regularized τ v) 0 :=
  (differentiableAt_originExtension τ hv).congr_of_eventuallyEq (regularized_origin_germ τ hv)

private theorem expression_add_one (τ : ℍ) {v z : ℂ}
    (hz : H τ z ≠ 0) (hzv : H τ (z + v) ≠ 0) :
    expression τ v (z + 1) = expression τ v z := by
  unfold expression
  rw [show (z + 1) + v = (z + v) + 1 by ring,
    L_add_one τ hz, L_add_one τ hzv, deriv_L_add_one τ hz, deriv_L_add_one τ hzv]

private theorem expression_add_tau (τ : ℍ) {v z : ℂ}
    (hz : H τ z ≠ 0) (hzv : H τ (z + v) ≠ 0) :
    expression τ v (z + τ) = expression τ v z := by
  unfold expression
  rw [show (z + (τ : ℂ)) + v = (z + v) + τ by ring,
    L_add_tau τ hz, L_add_tau τ hzv, deriv_L_add_tau τ hz, deriv_L_add_tau τ hzv]
  ring

theorem regularized_periodic_one (τ : ℍ) (v : ℂ) : Function.Periodic (regularized τ v) 1 := by
  intro z
  have he : (H τ (z + 1) = 0 ∨ H τ ((z + 1) + v) = 0) ↔
      (H τ z = 0 ∨ H τ (z + v) = 0) := by
    rw [show (z + 1) + v = (z + v) + 1 by ring, H_add_one, H_add_one]
    simp only [neg_eq_zero]
  by_cases hz : H τ z = 0 ∨ H τ (z + v) = 0
  · simp only [regularized, hz, he.mpr hz, if_true]
  · have hz0 : H τ z ≠ 0 := fun h => hz (Or.inl h)
    have hzv : H τ (z + v) ≠ 0 := fun h => hz (Or.inr h)
    simp only [regularized, hz, mt he.mp hz, if_false]
    exact expression_add_one τ hz0 hzv

private theorem H_tau_zero_iff (τ : ℍ) (z : ℂ) : H τ (z + τ) = 0 ↔ H τ z = 0 := by
  rw [H_shift_tau, mul_eq_zero]
  simp only [phase_ne_zero, false_or]

theorem regularized_periodic_tau (τ : ℍ) (v : ℂ) :
    Function.Periodic (regularized τ v) (τ : ℂ) := by
  intro z
  have he : (H τ (z + τ) = 0 ∨ H τ ((z + τ) + v) = 0) ↔
      (H τ z = 0 ∨ H τ (z + v) = 0) := by
    rw [show (z + (τ : ℂ)) + v = (z + v) + τ by ring,
      H_tau_zero_iff, H_tau_zero_iff]
  by_cases hz : H τ z = 0 ∨ H τ (z + v) = 0
  · simp only [regularized, hz, he.mpr hz, if_true]
  · have hz0 : H τ z ≠ 0 := fun h => hz (Or.inl h)
    have hzv : H τ (z + v) ≠ 0 := fun h => hz (Or.inr h)
    simp only [regularized, hz, mt he.mp hz, if_false]
    exact expression_add_tau τ hz0 hzv

private theorem expression_reflect (τ : ℍ) {v z : ℂ}
    (hz : H τ z ≠ 0) (hzv : H τ (z + v) ≠ 0) :
    expression τ v (-v - z) = expression τ v z := by
  unfold expression
  rw [show -v - z = -(z + v) by ring, show -(z + v) + v = -z by ring,
    L_neg τ hzv, L_neg τ hz, deriv_L_even τ hzv, deriv_L_even τ hz]
  ring

theorem regularized_reflect (τ : ℍ) (v z : ℂ) :
    regularized τ v (-v - z) = regularized τ v z := by
  have he : (H τ (-v - z) = 0 ∨ H τ ((-v - z) + v) = 0) ↔
      (H τ z = 0 ∨ H τ (z + v) = 0) := by
    rw [show -v - z = -(z + v) by ring, show -(z + v) + v = -z by ring, H_neg, H_neg]
    simp only [neg_eq_zero, or_comm]
  by_cases hz : H τ z = 0 ∨ H τ (z + v) = 0
  · simp only [regularized, hz, he.mpr hz, if_true]
  · have hz0 : H τ z ≠ 0 := fun h => hz (Or.inl h)
    have hzv : H τ (z + v) ≠ 0 := fun h => hz (Or.inr h)
    simp only [regularized, hz, mt he.mp hz, if_false]
    exact expression_reflect τ hz0 hzv

theorem differentiableAt_regularized_neg (τ : ℍ) {v : ℂ} (hv : H τ v ≠ 0) :
    DifferentiableAt ℂ (regularized τ v) (-v) := by
  have hd := differentiableAt_regularized_zero τ hv
  have he := HasDerivAt.comp_const_sub (-v) (-v)
    (by simpa only [sub_self] using hd.hasDerivAt)
  have hf : (fun z : ℂ => regularized τ v (-v - z)) = regularized τ v :=
    funext (regularized_reflect τ v)
  rw [hf] at he
  exact he.differentiableAt

private theorem differentiableAt_expression (τ : ℍ) {v z : ℂ}
    (hz : H τ z ≠ 0) (hzv : H τ (z + v) ≠ 0) :
    DifferentiableAt ℂ (expression τ v) z := by
  have hls := (HasDerivAt.comp_add_const z v (differentiableAt_L τ hzv).hasDerivAt).differentiableAt
  have hds := (HasDerivAt.comp_add_const z v
    (differentiableAt_deriv_L τ hzv).hasDerivAt).differentiableAt
  exact ((((differentiableAt_L τ hz).add_const (L τ v)).sub hls).pow 2 |>.add
    (differentiableAt_deriv_L τ hz) |>.add (differentiableAt_const (deriv (L τ) v))).add hds

private theorem differentiableAt_regularized_off (τ : ℍ) {v z : ℂ}
    (hz : H τ z ≠ 0) (hzv : H τ (z + v) ≠ 0) :
    DifferentiableAt ℂ (regularized τ v) z := by
  apply (differentiableAt_expression τ hz hzv).congr_of_eventuallyEq
  have hc : ContinuousAt (fun w : ℂ => H τ (w + v)) z :=
    ((differentiable_H τ).continuous.comp (continuous_id.add continuous_const)).continuousAt
  filter_upwards [((differentiable_H τ) z).continuousAt.eventually_ne hz,
    hc.eventually_ne hzv] with w hw hwv
  exact regularized_off τ hw hwv

private theorem differentiableAt_add_period {f : ℂ → ℂ} {p z : ℂ}
    (hp : Function.Periodic f p) (hf : DifferentiableAt ℂ f z) :
    DifferentiableAt ℂ f (z + p) := by
  have hd := HasDerivAt.comp_sub_const (z + p) p
    (by simpa only [add_sub_cancel_right] using hf.hasDerivAt)
  apply hd.differentiableAt.congr_of_eventuallyEq
  exact Eventually.of_forall fun w => by simpa only [sub_add_cancel] using hp (w - p)

/-- The actual extension is entire; every lattice pole is treated by the proved
local extension and genuine periods, not by total division at a pole. -/
theorem differentiable_regularized (τ : ℍ) {v : ℂ} (hv : H τ v ≠ 0) :
    Differentiable ℂ (regularized τ v) := by
  intro z
  have h1 := regularized_periodic_one τ v
  have ht := regularized_periodic_tau τ v
  by_cases hz : H τ z = 0
  · obtain ⟨m, n, he⟩ := (H_zero_iff_lattice τ z).mp hz
    rw [he]
    have hn := differentiableAt_add_period (ht.int_mul n) (differentiableAt_regularized_zero τ hv)
    have hm := differentiableAt_add_period (h1.int_mul m) hn
    simpa only [zero_add, add_zero, mul_one, add_comm] using hm
  · by_cases hzv : H τ (z + v) = 0
    · obtain ⟨m, n, he⟩ := (H_zero_iff_lattice τ (z + v)).mp hzv
      have hzrepr : z = ((-v) + (n : ℂ) * (τ : ℂ)) + (m : ℂ) := by
        linear_combination he
      rw [hzrepr]
      have hn := differentiableAt_add_period (ht.int_mul n) (differentiableAt_regularized_neg τ hv)
      have hm := differentiableAt_add_period (h1.int_mul m) hn
      simpa only [mul_one] using hm
    · exact differentiableAt_regularized_off τ hz hzv

/-- Direct completed-theta Frobenius–Stickelberger addition, on precisely the
nonzero theta-denominator domain. The constant is the actual finite part c. -/
theorem frobenius_stickelberger (τ : ℍ) (u v : ℂ)
    (hu : H τ u ≠ 0) (hv : H τ v ≠ 0) (huv : H τ (u + v) ≠ 0) :
    (L τ u + L τ v - L τ (u + v)) ^ 2 =
      -deriv (L τ) u - deriv (L τ) v - deriv (L τ) (u + v) + 3 * c τ := by
  have hd := differentiable_regularized τ hv
  have hb := QuasiThetaMultiplicationTwo.bounded_of_continuous_periodic hd.continuous
    (regularized_periodic_one τ v) (regularized_periodic_tau τ v)
  have he := hd.apply_eq_apply_of_bounded hb u 0
  rw [regularized_off τ hu huv, regularized_zero] at he
  unfold expression at he
  linear_combination he

end ZInQ.Contrib.HeckePrimeRationality.ThetaAddition
