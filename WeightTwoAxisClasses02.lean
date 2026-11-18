import WeightTwoAxisRows03
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinUnitSeries

/-!
# Actual signed one-dimensional congruence profiles

An injective congruence-class parametrization is used only in one dimension.
The absolutely convergent integer series is paired into positive and negative
indices, with the zero term checked literally. This identifies the constant
of the actual weight-two division form with the signed inverse-square axis
profile, independently of any primitive two-dimensional Eisenstein series.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open Complex Filter Matrix ModularForm
open UpperHalfPlane hiding I
open scoped Topology Real ModularForm MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants

open ZInQ.Contrib.HeckePrimeRationality

/-- The literal inverse-square series restricted to one integral congruence class. -/
def axisClass (N : ℕ) (b n : ℤ) : ℂ :=
  if (n : ZMod N) = (b : ZMod N) then 1 / (n : ℂ) ^ 2 else 0

/-- The two signed positive-index branches of the same one-dimensional series. -/
def signedAxisClass (N : ℕ) (b : ℤ) (d : ℕ) : ℂ :=
  ((d : ℂ) ^ 2)⁻¹ *
    ((if (d : ZMod N) = (b : ZMod N) then 1 else 0) +
      (if -(d : ZMod N) = (b : ZMod N) then 1 else 0))

/-- Every congruence-class term is supplied by a genuine one-dimensional index bijection. -/
theorem axisClass_hasSum (N : ℕ) (hN : 0 < N) (b : ℤ) :
    HasSum (axisClass N b) (∑' n : ℤ, 1 / ((b : ℂ) + (N : ℂ) * (n : ℂ)) ^ 2) := by
  let : NeZero N := ⟨hN.ne'⟩
  have hN0 : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hi : Function.Injective (fun n : ℤ => b + (N : ℤ) * n) := by
    intro n m h
    apply mul_left_cancel₀ hN0
    linarith
  apply (hi.hasSum_iff (f := axisClass N b) ?_).mp
  · change HasSum (fun n : ℤ => axisClass N b (b + (N : ℤ) * n)) _
    convert (axis_congruence_summable N hN b).hasSum using 1
    funext n
    have hc : ((b + (N : ℤ) * n : ℤ) : ZMod N) = (b : ZMod N) := by
      simp [Int.cast_add, Int.cast_mul, Int.cast_natCast]
    simp only [axisClass, hc, ite_true, Int.cast_add, Int.cast_mul, Int.cast_natCast]
  · intro n hn
    have hc : (n : ZMod N) ≠ (b : ZMod N) := by
      intro h
      obtain ⟨m, hm⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub n b N).mp h
      apply hn
      exact ⟨-m, by linarith⟩
    simp only [axisClass, ite_eq_right hc]

lemma axisClass_zero (N : ℕ) (b : ℤ) : axisClass N b 0 = 0 := by
  simp [axisClass]

lemma signedAxisClass_zero (N : ℕ) (b : ℤ) : signedAxisClass N b 0 = 0 := by
  simp [signedAxisClass]

lemma signedAxisClass_pair (N : ℕ) (b : ℤ) (d : ℕ) :
    axisClass N b (d : ℤ) + axisClass N b (-(d : ℤ)) = signedAxisClass N b d := by
  unfold axisClass signedAxisClass
  simp only [Int.cast_natCast, Int.cast_neg, neg_sq, one_div]
  split_ifs <;> ring

/-- Pairing is justified by the actual summability of the complete integer congruence class. -/
theorem axisClass_eq_signed_sum (N : ℕ) (hN : 0 < N) (b : ℤ) :
    (∑' n : ℤ, axisClass N b n) = ∑' d : ℕ, signedAxisClass N b d := by
  have hs := (axisClass_hasSum N hN b).summable
  have hp : Summable (fun d : ℕ+ => axisClass N b (d : ℤ)) :=
    (summable_pnat_iff_summable_nat).mpr (summable_int_iff_summable_nat_and_neg.mp hs).1
  have hm : Summable (fun d : ℕ+ => axisClass N b (-(d : ℤ))) :=
    (summable_pnat_iff_summable_nat).mpr (summable_int_iff_summable_nat_and_neg.mp hs).2
  rw [tsum_int_eq_zero_add_tsum_pnat hs, axisClass_zero, zero_add, ← hp.tsum_add hm]
  calc
    _ = ∑' d : ℕ+, signedAxisClass N b d := tsum_congr (fun d => signedAxisClass_pair N b d)
    _ = ∑' d : ℕ, signedAxisClass N b d :=
      tsum_pnat_eq_tsum_of_eq_zero (signedAxisClass_zero N b)

/-- The signed positive-index series is genuinely absolutely summable. -/
theorem signedAxisClass_summable (N : ℕ) (hN : 0 < N) (b : ℤ) :
    Summable (signedAxisClass N b) := by
  have hs := (axisClass_hasSum N hN b).summable
  exact ((summable_int_iff_summable_nat_and_neg.mp hs).1.add
    (summable_int_iff_summable_nat_and_neg.mp hs).2).congr (signedAxisClass_pair N b)

/-- The actual axis constant, at exactly the normalized principal period, is the signed series minus its finite part. -/
theorem normalized_axisConstant_eq_signed_sum (N : ℕ) (hN : 0 < N) (b : ℤ) (hb : ¬ (N : ℤ) ∣ b) :
    axisConstant N b / (N : ℂ) ^ 2 + (Real.pi : ℂ) ^ 2 / (3 * (N : ℂ) ^ 2) =
      ∑' d : ℕ, signedAxisClass N b d := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  rw [axisConstant_eq_congruence_row N hN b hb,
    ← (axisClass_hasSum N hN b).tsum_eq, axisClass_eq_signed_sum N hN b]
  field_simp [hN0]
  ring

#print axioms axisClass_hasSum
#print axioms axisClass_eq_signed_sum
#print axioms signedAxisClass_summable
#print axioms normalized_axisConstant_eq_signed_sum

end ZInQ.Contrib.HeckePrimeRationality.WeightTwoConstants
