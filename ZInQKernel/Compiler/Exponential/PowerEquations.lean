import ZInQKernel.Compiler.Exponential.AlphaEquations
import ZInQ.AlphaPowerModulus
import ZInQ.PowerBoundDraft

/-!
# The power formula (C.3)

Blueprint: `compiler/natural/exponential/power-equations.md`, `power-equations-correct.md`.

`PowEqns P Q R` separates the base zero and expresses `P = Q^R` for `Q > 0` through three alpha
formulas and one congruence (the AFP `exp_repr`). It holds exactly when `P = Q^R` (`0^0 = 1`).
-/

namespace ZInQ.AlphaPower

/-- The power formula (C.3): three branches, the last with witnesses `b, m, a₀, a₁, a₂`. -/
def PowEqns (P Q R : ℕ) : Prop :=
  (Q = 0 ∧ R = 0 ∧ P = 1) ∨ (Q = 0 ∧ 0 < R ∧ P = 0) ∨
    (0 < Q ∧ ∃ b m a0 a1 a2 : ℕ, AlphaEqns a0 (Q + 4) (R + 1) ∧ b = a0 + Q ^ 2 + 2 ∧
      m + Q ^ 2 + 1 = b * Q ∧ P < m ∧ AlphaEqns a1 b R ∧ AlphaEqns a2 b (R + 1) ∧
      (P + b * a1) % m = (Q * a1 + a2) % m)

/-- The power formula expresses exponentiation. -/
theorem powEqns_iff (P Q R : ℕ) : PowEqns P Q R ↔ P = Q ^ R := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · -- Base zero: only the first two branches can hold.
    unfold PowEqns
    rcases Nat.eq_zero_or_pos R with rfl | hR
    · simp
    · simp [hR.ne', hR]
  · have hQ' : Q ≠ 0 := hQ.ne'
    unfold PowEqns
    simp only [hQ', false_and, false_or, hQ, true_and]
    constructor
    · rintro ⟨b, m, a0, a1, a2, h0, rfl, hm, hPm, h1, h2, hcong⟩
      have ha0 := (alphaEqns_sound h0).2
      have ha1 := (alphaEqns_sound h1).2
      have ha2 := (alphaEqns_sound h2).2
      have hmZ : (m : ℤ) = ((a0 + Q ^ 2 + 2 : ℕ) : ℤ) * Q - (Q : ℤ) ^ 2 - 1 := by
        have : ((m + Q ^ 2 + 1 : ℕ) : ℤ) = (((a0 + Q ^ 2 + 2) * Q : ℕ) : ℤ) := by rw [hm]
        push_cast at this ⊢
        linarith
      -- `Q^R < m`.
      have hlt : (Q : ℤ) ^ R < m := by
        have := pow_lt_alphaZ_power_modulus Q R hQ
        rw [hmZ]; push_cast; rw [ha0]; exact this
      -- `m ∣ E_R - Q^R`.
      have hdvd := alphaZ_power_modulus_dvd (a0 + Q ^ 2 + 2) R (Q : ℤ)
      have hm' : ((a0 + Q ^ 2 + 2 : ℕ) : ℤ) * Q - Q * Q - 1 = m := by rw [hmZ]; ring
      rw [hm', ← ha1, ← ha2] at hdvd
      -- The congruence.
      have hc : (m : ℤ) ∣ ((Q * a1 + a2 : ℕ) : ℤ) - ((P + (a0 + Q ^ 2 + 2) * a1 : ℕ) : ℤ) :=
        (Nat.modEq_iff_dvd).mp hcong
      have hPQ : (m : ℤ) ∣ (P : ℤ) - (Q : ℤ) ^ R := by
        have := dvd_sub hdvd hc
        push_cast at this ⊢
        convert this using 1
        ring
      have hPm' : (P : ℤ) < m := by exact_mod_cast hPm
      have hP0 : (0 : ℤ) ≤ P := by positivity
      have hQ0 : (0 : ℤ) ≤ (Q : ℤ) ^ R := by positivity
      have h := Int.eq_zero_of_abs_lt_dvd hPQ (by rw [abs_lt]; constructor <;> linarith)
      have : (P : ℤ) = ((Q ^ R : ℕ) : ℤ) := by push_cast; linarith
      exact_mod_cast this
    · rintro rfl
      have hb0 : 3 < Q + 4 := by omega
      have ha0nn := alphaZ_nonneg (Q + 4) (by omega) (R + 1)
      set a0 := (alphaZ (Q + 4) (R + 1)).toNat with ha0def
      have ha0 : (a0 : ℤ) = alphaZ (Q + 4) (R + 1) := Int.toNat_of_nonneg ha0nn
      have ha0pos : 1 ≤ a0 := by
        have := alphaZ_ge_index (Q + 4) (R + 1) (by omega)
        omega
      set b := a0 + Q ^ 2 + 2 with hbdef
      have hQsq : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ
      have hb : 3 < b := by omega
      have hQ2 : Q ^ 2 + 1 ≤ b * Q := by
        have : b * 1 ≤ b * Q := Nat.mul_le_mul_left b hQ
        omega
      set m := b * Q - (Q ^ 2 + 1) with hmdef
      have hm : m + Q ^ 2 + 1 = b * Q := by omega
      have hmZ : (m : ℤ) = (b : ℤ) * Q - Q * Q - 1 := by
        have : ((m + Q ^ 2 + 1 : ℕ) : ℤ) = ((b * Q : ℕ) : ℤ) := by rw [hm]
        push_cast at this
        linear_combination this
      have hlt : ((Q ^ R : ℕ) : ℤ) < m := by
        have := pow_lt_alphaZ_power_modulus Q R hQ
        rw [hmZ, hbdef]; push_cast; rw [ha0]; linear_combination this
      have ha1nn := alphaZ_nonneg b (by omega) R
      have ha2nn := alphaZ_nonneg b (by omega) (R + 1)
      have ha1 : ((alphaZ b R).toNat : ℤ) = alphaZ b R := Int.toNat_of_nonneg ha1nn
      have ha2 : ((alphaZ b (R + 1)).toNat : ℤ) = alphaZ b (R + 1) := Int.toNat_of_nonneg ha2nn
      refine ⟨b, m, a0, (alphaZ b R).toNat, (alphaZ b (R + 1)).toNat,
        alphaEqns_complete _ _ hb0, rfl, hm, by exact_mod_cast hlt, alphaEqns_complete _ _ hb,
        alphaEqns_complete _ _ hb, ?_⟩
      have hdvd := alphaZ_power_modulus_dvd b R (Q : ℤ)
      rw [← hmZ] at hdvd
      apply (Nat.modEq_iff_dvd).mpr
      push_cast
      rw [ha1, ha2]
      convert hdvd using 1
      ring

end ZInQ.AlphaPower
