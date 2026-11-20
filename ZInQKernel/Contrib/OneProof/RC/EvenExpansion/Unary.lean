import ZInQKernel.Contrib.OneProof.RC.EvenExpansion.SeriesBounds
import ZInQKernel.Contrib.OneProof.RC.EvenBudget.Divided
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-! The convergent unary series; the remaining comparison is its weighted
Poisson transformation and cusp law. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenExpansion

open EvenBudget UpperHalfPlane
open scoped BigOperators Classical

/-- One of the two sign choices makes the unary character odd. -/
theorem exists_unary_parity {N : ℕ} (η : DirichletCharacter ℂ N) :
    ∃ i : Fin 2, η (-1 : ZMod N) * (-1 : ℂ) ^ i.val = -1 := by
  rcases η.even_or_odd with h | h
  · refine ⟨1, ?_⟩
    rw [show η (-1 : ZMod N) = 1 from h]
    norm_num
  · refine ⟨0, ?_⟩
    rw [show η (-1 : ZMod N) = -1 from h]
    norm_num

private theorem unary_shell {good : ℕ → Prop} (η : ℕ → ℂ) (i : Fin 2)
    {j k : ℕ} (hj : 0 < j) (hk : k ≠ 0) :
    unaryCoeff good η i j (j * k ^ 2) =
      if ∀ p ∈ k.primeFactors, good p then η k * (ThetaCoeff.unaryWeight i k : ℂ) else 0 := by
  classical
  by_cases hgood : ∀ p ∈ k.primeFactors, good p
  · let h : ∃ t : ℕ, t ≠ 0 ∧ (∀ p ∈ t.primeFactors, good p) ∧ j * k ^ 2 = j * t ^ 2 :=
      ⟨k, hk, hgood, rfl⟩
    rw [unaryCoeff, dite_eq_left h, ite_eq_left hgood]
    have he : k = h.choose :=
      Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
        (Nat.eq_of_mul_eq_mul_left hj h.choose_spec.2.2)
    rw [← he]
  · rw [unaryCoeff, ite_eq_right hgood, dite_eq_right]
    rintro ⟨t, _, ht, he⟩
    have he : k = t :=
      Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0)
        (Nat.eq_of_mul_eq_mul_left hj he)
    exact hgood (he.symm ▸ ht)

/-- The actual unary function given by the exact even correction coefficients. -/
def unaryFun {N : ℕ} (good : ℕ → Prop) (η : DirichletCharacter ℂ N) (i : Fin 2)
    (j : ℕ) (z : ℍ) : ℂ :=
  ∑' n, unaryCoeff good (fun k => η k) i j n * Function.Periodic.qParam 1 (z : ℂ) ^ n

/-- Convergence at every point of the upper half plane, including the exact
zero values off the positive, coprime square shell. -/
theorem unary_hasSum {N : ℕ} [NeZero N] (good : ℕ → Prop) (η : DirichletCharacter ℂ N)
    (i : Fin 2) {j : ℕ} (hj : 0 < j) (z : ℍ) :
    HasSum (fun n => unaryCoeff good (fun k => η k) i j n *
      Function.Periodic.qParam 1 (z : ℂ) ^ n) (unaryFun good η i j z) := by
  classical
  apply Summable.hasSum
  apply summable_squareShell hj
  · intro n hn
    rw [unaryCoeff, dite_eq_right]
    rintro ⟨k, hk, _, rfl⟩
    exact hn ⟨k - 1, by simp only [Nat.sub_add_cancel (Nat.pos_of_ne_zero hk)]⟩
  · intro k
    rw [unary_shell _ _ hj (Nat.succ_ne_zero _)]
    split_ifs
    · rw [norm_mul, ThetaCoeff.unaryWeight, Int.cast_mul, Int.cast_pow, norm_mul,
        norm_pow, Int.cast_natCast, Complex.norm_natCast]
      have hχ := η.norm_le_one ((k + 1 : ℕ) : ZMod N)
      have hsign : ‖(jacobiSym (-1) (k + 1) : ℂ)‖ ≤ 1 := by
        rcases jacobiSym.trichotomy (-1) (k + 1) with h | h | h <;> simp [h]
      have hc : ‖(jacobiSym (-1) (k + 1) : ℂ)‖ ^ i.val ≤ 1 := pow_le_one₀ (norm_nonneg _) hsign
      calc
        _ ≤ 1 * (1 * ((k + 1 : ℕ) : ℝ)) :=
          mul_le_mul hχ (mul_le_mul_of_nonneg_right hc (by positivity))
            (by positivity) zero_le_one
        _ = _ := by simp
    · simpa only [norm_zero] using (Nat.cast_nonneg (α := ℝ) (k + 1))
  · exact Function.Periodic.norm_qParam_lt_one one_pos z.im_pos


end ZInQ.Manuscript.RC.EvenExpansion
