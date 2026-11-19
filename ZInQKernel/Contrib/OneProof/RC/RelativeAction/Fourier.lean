import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Local

/-! Finite Fourier inversion. The finite reindexing is on-the-spot (c) for tex 8653. -/

noncomputable section

namespace ZInQ.Manuscript.RC.RelativeAction

open OldStageLaw Complex
open scoped BigOperators

variable {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]

private theorem pairing_symm (r s : Grid a) : pairing r s = pairing s r := by
  simp only [pairing, mul_comm]

private def pairingChar (s : Grid a) : AddChar (Grid a) ℂ where
  toFun r := pairing r s
  map_zero_eq_one' := by simp [pairing]
  map_add_eq_mul' r t := pairing_add_left r t s

private theorem pairingChar_eq_zero (s : Grid a) : pairingChar s = 0 ↔ s = 0 := by
  constructor
  · intro h
    funext i
    have hi := congrArg (fun χ : AddChar (Grid a) ℂ => χ (Pi.single i (1 : ZMod (2 * a i)))) h
    change pairing (Pi.single i 1) s = 1 at hi
    have hp : pairing (Pi.single i 1) s = ZMod.stdAddChar (-(s i)) := by
      unfold pairing
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj
        simp [Pi.single_eq_of_ne hj]
      · simp
    rw [hp, ← (ZMod.stdAddChar (N := 2 * a i)).map_zero_eq_one,
      ZMod.injective_stdAddChar.eq_iff, neg_eq_zero] at hi
    exact hi
  · rintro rfl
    ext r
    simp [pairingChar, pairing]

private theorem sum_pairing (s : Grid a) :
    ∑ r : Grid a, pairing r s = if s = 0 then (Fintype.card (Grid a) : ℂ) else 0 := by
  classical
  change (∑ r, pairingChar s r) = _
  simpa only [pairingChar_eq_zero] using AddChar.sum_eq_ite (pairingChar s)

private theorem normalization_sq :
    (∏ i, 1 / (2 * (a i : ℂ)) ^ (1 / 2 : ℂ)) *
      (∏ i, 1 / (2 * (a i : ℂ)) ^ (1 / 2 : ℂ)) * (Fintype.card (Grid a) : ℂ) = 1 := by
  rw [Fintype.card_pi, Nat.cast_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun i _ => ?_
  have ha : a i ≠ 0 := by
    intro h
    exact NeZero.ne (2 * a i) (by simp [h])
  have h : (2 * (a i : ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr ha)
  have hs : (2 * (a i : ℂ)) ^ (1 / 2 : ℂ) * (2 * (a i : ℂ)) ^ (1 / 2 : ℂ) =
      2 * (a i : ℂ) := by
    rw [← Complex.cpow_add _ _ h, show (1 / 2 + 1 / 2 : ℂ) = 1 by norm_num, Complex.cpow_one]
  rw [ZMod.card, div_mul_div_comm, one_mul, hs, one_div]
  push_cast
  exact inv_mul_cancel₀ h

/-- The square of the normalized grid Fourier transform is reflection. -/
theorem finiteFourier_sq (w : Grid a → ℂ) :
    finiteFourier (finiteFourier w) = fun r => w (-r) := by
  classical
  funext s
  let C : ℂ := ∏ i, 1 / (2 * (a i : ℂ)) ^ (1 / 2 : ℂ)
  change C * ∑ r, (C * ∑ t, w t * pairing t r) * pairing r s = w (-s)
  calc
    _ = C * C * ∑ t, w t * ∑ r, pairing r (t + s) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun r _ => ?_
      rw [pairing_symm r (t + s), pairing_add_left, pairing_symm s r]
      ring
    _ = _ := by
      simp only [sum_pairing, add_eq_zero_iff_eq_neg, mul_ite, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true]
      have h : C * C * (Fintype.card (Grid a) : ℂ) = 1 := normalization_sq (a := a)
      rw [mul_left_comm (C * C), h, mul_one]

/-- Four successive inversions act as the identity on the full grid. -/
theorem finiteFourier_four (w : Grid a → ℂ) :
    finiteFourier (finiteFourier (finiteFourier (finiteFourier w))) = w := by
  have h := finiteFourier_sq (finiteFourier (finiteFourier w))
  rw [h]
  funext r
  rw [congrFun (finiteFourier_sq w) (-r), neg_neg]

#print axioms pairing_symm
#print axioms pairingChar_eq_zero
#print axioms sum_pairing
#print axioms normalization_sq
#print axioms finiteFourier_sq
#print axioms finiteFourier_four

end ZInQ.Manuscript.RC.RelativeAction
