import ZInQKernel.Contrib.OneProof.RC.EisSlash.Characters

/-! Cancellation of the common weight-two correction for a pair with a
nontrivial character. This computation is on-the-spot (c) for the
Eisenstein constituent step of tex 9647–9654, 9762–9764 and 9862–9864. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EisSlash

open Matrix O12Eisenstein O12EisConst EisForm

private def splitResidue (m₁ m₂ : ℕ) [NeZero m₁] [NeZero m₂] :
    ZMod m₁ × ZMod m₂ ≃ ZMod (m₂ * m₁) :=
  ((ZMod.finEquiv m₁).symm.toEquiv.prodCongr (ZMod.finEquiv m₂).symm.toEquiv).trans
    (finProdFinEquiv.trans ((finCongr (mul_comm m₁ m₂)).trans (ZMod.finEquiv _).toEquiv))

private theorem splitResidue_val (m₁ m₂ : ℕ) [NeZero m₁] [NeZero m₂]
    (x : ZMod m₁) (y : ZMod m₂) :
    (splitResidue m₁ m₂ (x,y)).val = y.val + m₂ * x.val := by
  cases m₁ with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ m₁ =>
    cases m₂ with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ m₂ => rfl

private theorem sum_residue_second {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂]
    (b : DirichletCharacter ℂ m₂) :
    (∑ r : ZMod (m₂ * m₁), b⁻¹ (r.val : ZMod m₂)) =
      (m₁ : ℂ) * ∑ r : ZMod m₂, b⁻¹ r := by
  rw [← (splitResidue m₁ m₂).sum_comp, Fintype.sum_prod_type]
  simp only [splitResidue_val, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self,
    zero_mul, add_zero, ZMod.natCast_zmod_val, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul]

private theorem sum_residue_first {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂]
    (a : DirichletCharacter ℂ m₁) :
    (∑ r : ZMod (m₂ * m₁), if m₂ ∣ r.val then a ((r.val / m₂ : ℕ) : ZMod m₁) else 0) =
      ∑ r : ZMod m₁, a r := by
  classical
  rw [← (splitResidue m₁ m₂).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [splitResidue_val, Nat.dvd_add_left (dvd_mul_right m₂ r.val)]
  rw [Finset.sum_eq_single (0 : ZMod m₂)]
  · simp [NeZero.ne m₂]
  · intro s _ hne
    have hnd : ¬ m₂ ∣ s.val := fun h =>
      hne (by simpa only [ZMod.natCast_zmod_val] using
        (ZMod.natCast_eq_zero_iff s.val m₂).mpr h)
    simp [hnd]
  · simp

/-- A nontrivial factor kills the total coefficient of the reference
lattice, in either Fourier order. -/
theorem characterWeight_sum_zero {m₁ m₂ N : ℕ} [NeZero m₁] [NeZero m₂] [NeZero N]
    (hN : N = m₂ * m₁) (a : DirichletCharacter ℂ m₁) (b : DirichletCharacter ℂ m₂)
    (hn : a ≠ 1 ∨ b ≠ 1) :
    ∑ r : Fin 2 → ZMod N, characterWeight a b r = 0 := by
  subst N
  rw [← (finTwoArrowEquiv (ZMod (m₂ * m₁))).symm.sum_comp, Fintype.sum_prod_type]
  have h (r s : ZMod (m₂ * m₁)) : characterWeight a b ![r,s] =
      (if m₂ ∣ r.val then a ((r.val / m₂ : ℕ) : ZMod m₁) else 0) *
        b⁻¹ (s.val : ZMod m₂) := by
    simp only [characterWeight, rowWeight, residueLift, cons_val_zero, cons_val_one,
      Int.natCast_dvd_natCast, ← Int.natCast_ediv, Int.cast_natCast, ite_mul, zero_mul]
  simp_rw [finTwoArrowEquiv_symm_apply, h, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [sum_residue_first, sum_residue_second]
  rcases hn with ha | hb
  · rw [MulChar.sum_eq_zero_of_ne_one ha, zero_mul]
  · have hbi : b⁻¹ ≠ 1 := by simpa
    rw [MulChar.sum_eq_zero_of_ne_one hbi, mul_zero, mul_zero]


end ZInQ.Manuscript.RC.EisSlash
