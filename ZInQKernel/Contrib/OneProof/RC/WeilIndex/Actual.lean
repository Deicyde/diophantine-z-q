import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Product
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.Determinant
import ZInQKernel.Contrib.OneProof.RC.WeilIndex.ResidueHaar

/-! Finiteness and unit determinant defects for the actual normalized
oscillatory indices, independent of the remaining signed odd Gauss evaluation.
The arithmetic calculation is on-the-spot (c), tex 8891–8901, 9000–9004. -/

noncomputable section

namespace ZInQ.Manuscript.RC.WeilIndex

open Intertwine Intertwine2

private theorem gaussGamma_of_even (p : Place) (hp : p ≠ dyadicPlace) (a : ℚ_[p.val]ˣ)
    (ha : valAt p a % 2 = 0) : gaussGamma p a = 1 := by
  rw [gaussGamma, dite_eq_right (fun h => h.2 ha), finiteGamma_even_odd_place p hp a ha]

/-- The actual finite scalar is one away from two and the prime divisors
of the numerator and denominator of a rational coefficient. -/
theorem gaussGamma_rational_finite (q : ℚˣ) :
    (fun p => gaussGamma p (atPrime p q)).HasFiniteMulSupport := by
  let r := (q : ℚ)
  have hn : r.num.natAbs * r.den ≠ 0 := mul_ne_zero
    (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr q.ne_zero)) r.den_nz
  have hs : Set.Finite {p : ℕ | p ∣ r.num.natAbs * r.den} :=
    (Set.finite_Iic _).subset (fun x hx => Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hx)
  have hpre := hs.preimage (Subtype.val_injective (p := fun n : ℕ => n.Prime)).injOn
  refine ((Set.finite_singleton dyadicPlace).union hpre).subset ?_
  intro p hp
  by_contra hnot
  rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_preimage, Set.mem_ofPred_eq, not_or] at hnot
  have hnum : ¬ p.val ∣ r.num.natAbs := fun h => hnot.2 (dvd_mul_of_dvd_left h _)
  have hden : ¬ p.val ∣ r.den := fun h => hnot.2 (dvd_mul_of_dvd_right h _)
  have hz : valAt p (atPrime p q) = 0 := by
    change ((r : ℚ_[p.val])).valuation = 0
    rw [Padic.valuation_ratCast, padicValRat_def, padicValInt,
      padicValNat.eq_zero_of_not_dvd hnum, padicValNat.eq_zero_of_not_dvd hden]
    rfl
  exact hp (gaussGamma_of_even p hnot.1 _ (by rw [hz]; decide))

/-- Finiteness of the product for the actual finite Weil indices, for
every nondegenerate rational diagonal list. -/
theorem gaussGamma_indexAt_finite (q : List ℚˣ) :
    (indexAt gaussGamma q).HasFiniteMulSupport := by
  induction q with
  | nil =>
      have hx : indexAt gaussGamma [] = 1 := rfl
      simp [hx, Function.HasFiniteMulSupport]
  | cons a q ih =>
      change ((fun p => gaussGamma p (atPrime p a)) * indexAt gaussGamma q).HasFiniteMulSupport
      exact (gaussGamma_rational_finite a).mul ih

/-- For the actual odd-prime Weil indices the unknown base Gauss sign
cancels from the four-index quotient on units. -/
theorem gaussGamma_odd_unit_defect (p : Place) (hp : p ≠ dyadicPlace)
    (u a : ℚ_[p.val]ˣ) (hu : valAt p u = 0) :
    ((gaussGamma p 1 * gaussGamma p (u * a) /
      (gaussGamma p u * gaussGamma p a) : ℂˣ) : ℂ) =
      if valAt p a % 2 = 0 then 1 else
        (quadraticChar (ZMod p.val) (oddUnitResidue p u : ZMod p.val) : ℂ) := by
  have h1 : valAt p 1 = 0 := by simp [valAt]
  have hva : valAt p (u * a) = valAt p a := by rw [valAt_mul, hu, zero_add]
  rw [gaussGamma_of_even p hp 1 (by rw [h1]; decide),
    gaussGamma_of_even p hp u (by rw [hu]; decide), one_mul, one_mul]
  by_cases ha : valAt p a % 2 = 0
  · rw [gaussGamma_of_even p hp a ha,
      gaussGamma_of_even p hp (u * a) (by simpa only [hva] using ha),
      ite_eq_left ha, div_one, Units.val_one]
  · have hau : valAt p (u * a) % 2 ≠ 0 := by simpa only [hva] using ha
    rw [ite_eq_right ha, Units.val_div_eq_div_val]
    simp only [gaussGamma, dite_eq_left (And.intro hp ha), dite_eq_left (And.intro hp hau),
      Units.val_mk0]
    have hp2 : p.val ≠ 2 := fun h => hp (Subtype.ext h)
    have htw (b : (ZMod p.val)ˣ) :
        oddGauss p b = (quadraticChar (ZMod p.val) (b : ZMod p.val) : ℂ) * oddGauss p 1 :=
      oddGauss_twist p hp2 b
    have hne : oddGauss p (oddUnitResidue p a) ≠ 0 := by
      have h := (gaussGamma p a).ne_zero
      rwa [gaussGamma, dite_eq_left ⟨hp, ha⟩, Units.val_mk0] at h
    apply (div_eq_iff hne).2
    rw [htw (oddUnitResidue p (u * a)), htw (oddUnitResidue p a),
      oddUnitResidue_mul, Units.val_mul, map_mul, Int.cast_mul, mul_assoc]

/-- The actual dyadic quotient on two units is the sign predicted by
the quadratic Hilbert symbol at two. -/
theorem gaussGamma_dyadic_unit_defect (u a : ℚ_[dyadicPlace.val]ˣ)
    (hu : valAt dyadicPlace u = 0) (ha : valAt dyadicPlace a = 0) :
    gaussGamma dyadicPlace 1 * gaussGamma dyadicPlace (u * a) /
      (gaussGamma dyadicPlace u * gaussGamma dyadicPlace a) =
      exponentRoot (if ZMod.χ₄ (ZMod.cast (dyadicUnitResidue u : ZMod 8)) = -1 ∧
        ZMod.χ₄ (ZMod.cast (dyadicUnitResidue a : ZMod 8)) = -1 then 4 else 0) := by
  simp only [gaussGamma, ne_eq, not_true_eq_false, false_and, dite_false]
  rw [← determinantExponent_value, dyadic_unit_determinantExponent u a hu ha]

#print axioms gaussGamma_of_even
#print axioms gaussGamma_rational_finite
#print axioms gaussGamma_indexAt_finite
#print axioms gaussGamma_odd_unit_defect
#print axioms gaussGamma_dyadic_unit_defect

end ZInQ.Manuscript.RC.WeilIndex
