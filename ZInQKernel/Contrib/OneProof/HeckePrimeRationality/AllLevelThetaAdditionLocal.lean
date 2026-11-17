import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaMultiplicationTwo
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Direct addition analysis for the completed odd theta function

The logarithmic derivative and its finite part below are defined from the actual
completed theta function. Statements involving the logarithmic derivative are
restricted to nonzero denominator values. Local divided differences provide
analytic extensions, rather than assigning a quotient a value at a pole.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Function
open scoped Topology Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.ThetaAddition

open CompletedTheta

/-- The actual logarithmic derivative, used only off the theta zero set. -/
def L (τ : ℍ) (z : ℂ) : ℂ := deriv (H τ) z / H τ z

/-- The entire factor obtained by removing the simple origin zero. -/
def A (τ : ℍ) : ℂ → ℂ := dslope (H τ) 0

/-- The regular logarithmic part near the origin. -/
def h (τ : ℍ) (z : ℂ) : ℂ := deriv (A τ) z / A τ z

/-- The actual derivative of the regular part at the origin. -/
def c (τ : ℍ) : ℂ := deriv (h τ) 0

private theorem deriv_differentiableAt_of_eventually
    {f : ℂ → ℂ} {z : ℂ}
    (hf : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w) :
    DifferentiableAt ℂ (deriv f) z := by
  obtain ⟨s, hs, ho, hz⟩ := eventually_nhds_iff.mp hf
  have hd : DifferentiableOn ℂ f s := fun w hw => (hs w hw).differentiableWithinAt
  exact (hd.deriv ho).differentiableAt (ho.mem_nhds hz)

private theorem dslope_differentiableAt_of_eventually
    {f : ℂ → ℂ} {z : ℂ}
    (hf : ∀ᶠ w in 𝓝 z, DifferentiableAt ℂ f w) :
    DifferentiableAt ℂ (dslope f z) z := by
  obtain ⟨s, hs, ho, hz⟩ := eventually_nhds_iff.mp hf
  have hd : DifferentiableOn ℂ f s := fun w hw => (hs w hw).differentiableWithinAt
  exact ((Complex.differentiableOn_dslope (ho.mem_nhds hz)).mpr hd).differentiableAt
    (ho.mem_nhds hz)

theorem differentiable_A (τ : ℍ) : Differentiable ℂ (A τ) :=
  QuasiThetaMultiplicationTwo.differentiable_dslope (differentiable_H τ) 0

theorem A_zero (τ : ℍ) : A τ 0 = deriv (H τ) 0 := by
  simp only [A, dslope_same]

theorem A_zero_ne_zero (τ : ℍ) : A τ 0 ≠ 0 := by
  rw [A_zero]
  exact deriv_H_zero_ne_zero τ

/-- The undivided origin factorization holds also at the origin. -/
theorem factorization (τ : ℍ) (z : ℂ) : z * A τ z = H τ z := by
  simpa only [A, sub_zero, H_zero, smul_eq_mul] using sub_smul_dslope (H τ) 0 z

theorem A_even (τ : ℍ) (z : ℂ) : A τ (-z) = A τ z := by
  by_cases hz : z = 0
  · subst z
    simp
  have hn : (-z) * A τ (-z) = -(z * A τ z) := by
    rw [factorization, factorization, H_neg]
  apply mul_left_cancel₀ hz
  linear_combination -hn

theorem deriv_A_zero (τ : ℍ) : deriv (A τ) 0 = 0 := by
  have ha : HasDerivAt (fun w : ℂ => A τ (-w)) (-deriv (A τ) 0) 0 := by
    simpa only [Function.comp_def, Pi.neg_apply, neg_zero, id_eq, mul_neg, mul_one] using
      ((differentiable_A τ) (-(0 : ℂ))).hasDerivAt.comp
        (h₂ := A τ) (h := fun w : ℂ => -w) (0 : ℂ) (hasDerivAt_id (0 : ℂ)).neg
  have hb : HasDerivAt (fun w : ℂ => A τ (-w)) (deriv (A τ) 0) 0 :=
    ((differentiable_A τ) 0).hasDerivAt.congr_of_eventuallyEq
      (Eventually.of_forall (A_even τ))
  have he := ha.unique hb
  linear_combination -he / 2

theorem h_zero (τ : ℍ) : h τ 0 = 0 := by
  simp only [h, deriv_A_zero, zero_div]

private theorem point_ne_zero (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) : z ≠ 0 := by
  rintro rfl
  exact hz (H_zero τ)

private theorem A_ne_zero_of_H_ne_zero (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) : A τ z ≠ 0 := by
  intro ha
  apply hz
  rw [← factorization, ha, mul_zero]

theorem differentiableAt_h (τ : ℍ) {z : ℂ} (hz : A τ z ≠ 0) :
    DifferentiableAt ℂ (h τ) z :=
  ((differentiable_A τ).deriv z).div ((differentiable_A τ) z) hz

theorem differentiableAt_L (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) :
    DifferentiableAt ℂ (L τ) z :=
  ((differentiable_H τ).deriv z).div ((differentiable_H τ) z) hz

private theorem deriv_H_factorization (τ : ℍ) (z : ℂ) :
    deriv (H τ) z = A τ z + z * deriv (A τ) z := by
  have hd := (hasDerivAt_id z).mul ((differentiable_A τ) z).hasDerivAt
  have he : (fun w : ℂ => w * A τ w) = H τ := funext (factorization τ)
  change HasDerivAt (fun w : ℂ => w * A τ w)
    (1 * A τ z + z * deriv (A τ) z) z at hd
  rw [he] at hd
  simpa only [one_mul] using hd.deriv

/-- The logarithmic derivative has residue one and the actual regular part h. -/
theorem L_split (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) :
    L τ z = 1 / z + h τ z := by
  have hz0 := point_ne_zero τ hz
  have ha := A_ne_zero_of_H_ne_zero τ hz
  unfold L h
  rw [deriv_H_factorization, ← factorization]
  field_simp

/-- Differentiating the local split is justified on a zero-free neighborhood. -/
theorem deriv_L_split (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) :
    deriv (L τ) z = -(z ^ 2)⁻¹ + deriv (h τ) z := by
  have he : L τ =ᶠ[𝓝 z] fun w : ℂ => w⁻¹ + h τ w := by
    filter_upwards [((differentiable_H τ) z).continuousAt.eventually_ne hz] with w hw
    simpa only [one_div] using L_split τ hw
  have hd := ((hasDerivAt_inv (point_ne_zero τ hz)).add
    (differentiableAt_h τ (A_ne_zero_of_H_ne_zero τ hz)).hasDerivAt).congr_of_eventuallyEq he
  exact hd.deriv

theorem differentiableAt_deriv_h (τ : ℍ) {z : ℂ} (hz : A τ z ≠ 0) :
    DifferentiableAt ℂ (deriv (h τ)) z := by
  apply deriv_differentiableAt_of_eventually
  filter_upwards [((differentiable_A τ) z).continuousAt.eventually_ne hz] with w hw
  exact differentiableAt_h τ hw

theorem differentiableAt_deriv_L (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) :
    DifferentiableAt ℂ (deriv (L τ)) z := by
  apply deriv_differentiableAt_of_eventually
  filter_upwards [((differentiable_H τ) z).continuousAt.eventually_ne hz] with w hw
  exact differentiableAt_L τ hw

/-- The analytic numerator of the regularized origin expression. -/
def a (τ : ℍ) (v z : ℂ) : ℂ := h τ z + L τ v - L τ (z + v)

theorem a_zero (τ : ℍ) (v : ℂ) : a τ v 0 = 0 := by
  simp [a, h_zero]

private theorem shift_zero_free (τ : ℍ) {v : ℂ} (hv : H τ v ≠ 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ), H τ (z + v) ≠ 0 := by
  have hc : ContinuousAt (fun z : ℂ => H τ (z + v)) 0 :=
    ((differentiable_H τ).continuous.comp (continuous_id.add continuous_const)).continuousAt
  exact hc.eventually_ne (by simpa only [zero_add] using hv)

private theorem differentiableAt_a (τ : ℍ) (v : ℂ) {z : ℂ}
    (hz : A τ z ≠ 0) (hzv : H τ (z + v) ≠ 0) :
    DifferentiableAt ℂ (a τ v) z := by
  exact ((differentiableAt_h τ hz).add_const (L τ v)).sub
    (HasDerivAt.comp_add_const z v (differentiableAt_L τ hzv).hasDerivAt).differentiableAt

private theorem a_eventually_differentiable (τ : ℍ) {v : ℂ} (hv : H τ v ≠ 0) :
    ∀ᶠ z in 𝓝 (0 : ℂ), DifferentiableAt ℂ (a τ v) z := by
  filter_upwards [((differentiable_A τ) 0).continuousAt.eventually_ne (A_zero_ne_zero τ),
    shift_zero_free τ hv] with z hz hzv
  exact differentiableAt_a τ v hz hzv

theorem hasDerivAt_a_zero (τ : ℍ) {v : ℂ} (hv : H τ v ≠ 0) :
    HasDerivAt (a τ v) (c τ - deriv (L τ) v) 0 := by
  have hvd : HasDerivAt (fun z : ℂ => L τ (z + v)) (deriv (L τ) v) 0 :=
    HasDerivAt.comp_add_const (0 : ℂ) v
      (by simpa only [zero_add] using (differentiableAt_L τ hv).hasDerivAt)
  exact ((differentiableAt_h τ (A_zero_ne_zero τ)).hasDerivAt.add_const (L τ v)).sub hvd

/-- The original meromorphic addition expression, restricted in theorems to
nonzero theta denominators. -/
def expression (τ : ℍ) (v z : ℂ) : ℂ :=
  (L τ z + L τ v - L τ (z + v)) ^ 2 +
    deriv (L τ) z + deriv (L τ) v + deriv (L τ) (z + v)

/-- Explicit local extension at the origin, constructed with a divided difference. -/
def originExtension (τ : ℍ) (v z : ℂ) : ℂ :=
  2 * dslope (a τ v) 0 z + a τ v z ^ 2 +
    deriv (h τ) z + deriv (L τ) v + deriv (L τ) (z + v)

theorem differentiableAt_originExtension (τ : ℍ) {v : ℂ} (hv : H τ v ≠ 0) :
    DifferentiableAt ℂ (originExtension τ v) 0 := by
  have hds := dslope_differentiableAt_of_eventually (a_eventually_differentiable τ hv)
  have had := (hasDerivAt_a_zero τ hv).differentiableAt
  have hhd := differentiableAt_deriv_h τ (A_zero_ne_zero τ)
  have hld : DifferentiableAt ℂ (fun z : ℂ => deriv (L τ) (z + v)) 0 :=
    (HasDerivAt.comp_add_const (0 : ℂ) v
      (by simpa only [zero_add] using (differentiableAt_deriv_L τ hv).hasDerivAt)).differentiableAt
  exact ((((hds.const_mul (2 : ℂ)).add (had.pow 2)).add hhd).add
    (differentiableAt_const (deriv (L τ) v))).add hld

/-- The finite part is the actual derivative-defined constant 3c. -/
theorem originExtension_zero (τ : ℍ) {v : ℂ} (hv : H τ v ≠ 0) :
    originExtension τ v 0 = 3 * c τ := by
  simp only [originExtension, dslope_same, a_zero, zero_pow (by decide : 2 ≠ 0),
    add_zero, zero_add]
  rw [(hasDerivAt_a_zero τ hv).deriv]
  unfold c
  ring

/-- Exact pole cancellation on the stated off-zero domain. -/
theorem expression_eq_originExtension (τ : ℍ) {v z : ℂ}
    (hv : H τ v ≠ 0) (hz : H τ z ≠ 0) (hzv : H τ (z + v) ≠ 0) :
    expression τ v z = originExtension τ v z := by
  have hz0 := point_ne_zero τ hz
  have hs : L τ z + L τ v - L τ (z + v) = z⁻¹ + a τ v z := by
    rw [L_split τ hz]
    unfold a
    rw [one_div]
    ring
  have hfac : z * dslope (a τ v) 0 z = a τ v z := by
    simpa only [sub_zero, a_zero, smul_eq_mul] using sub_smul_dslope (a τ v) 0 z
  have hds : dslope (a τ v) 0 z = a τ v z / z := by
    apply (eq_div_iff hz0).mpr
    simpa only [mul_comm] using hfac
  unfold expression originExtension
  rw [hs, deriv_L_split τ hz, hds]
  field_simp
  ring

/-- A proved local analytic extension with the actual finite part; no global
addition identity is assumed. The punctured neighborhood is genuinely off poles. -/
theorem origin_local_extension (τ : ℍ) {v : ℂ} (hv : H τ v ≠ 0) :
    DifferentiableAt ℂ (originExtension τ v) 0 ∧ originExtension τ v 0 = 3 * c τ ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), H τ z ≠ 0 ∧ H τ (z + v) ≠ 0 ∧
        expression τ v z = originExtension τ v z := by
  refine ⟨differentiableAt_originExtension τ hv, originExtension_zero τ hv, ?_⟩
  have hA := ((differentiable_A τ) 0).continuousAt.eventually_ne (A_zero_ne_zero τ)
  filter_upwards [hA.filter_mono nhdsWithin_le_nhds,
    (shift_zero_free τ hv).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z haz hzv hz0
  have hz : H τ z ≠ 0 := by
    rw [← factorization]
    exact mul_ne_zero hz0 haz
  exact ⟨hz, hzv, expression_eq_originExtension τ hv hz hzv⟩

theorem tendsto_expression_origin (τ : ℍ) {v : ℂ} (hv : H τ v ≠ 0) :
    Tendsto (expression τ v) (𝓝[≠] (0 : ℂ)) (𝓝 (3 * c τ)) := by
  obtain ⟨hd, hzero, he⟩ := origin_local_extension τ hv
  have ht : Tendsto (originExtension τ v) (𝓝[≠] (0 : ℂ)) (𝓝 (originExtension τ v 0)) :=
    hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [hzero] at ht
  exact ht.congr' (he.mono fun z hz => hz.2.2.symm)

end ZInQ.Contrib.HeckePrimeRationality.ThetaAddition
