import ZInQKernel.Contrib.OneProof.RC.WitnessSpec.Residue
import Mathlib.NumberTheory.LegendreSymbol.Basic

/-! Choose the residue square root induced by the exact place; its sign is
inherited from the global root. This is the scalar in the split identification
of tex 8393–8394. -/

noncomputable section

open ZInQ.Contrib.ChebFD.C10 (Zbar GQ)

namespace ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace

attribute [local instance] Ideal.Quotient.field

variable {g : GQ} {p : ℕ} [Fact p.Prime] (v : FrobeniusPlace g p)

/-- The reduction of a specified square root of D is the image of a
nonzero square root in the prime field when the stage has positive sign. -/
theorem split_root_over_primeField {D : ℤ} (hD : ¬ (p : ℤ) ∣ D)
    (hsplit : legendreSym p D = 1) (s : Zbar) (hs : s ^ 2 = (D : Zbar)) :
    ∃ a : ZMod p, a ≠ 0 ∧ a ^ 2 = (D : ZMod p) ∧
      algebraMap (ZMod p) (Zbar ⧸ v.prime) a = Ideal.Quotient.mk v.prime s := by
  let q := Ideal.Quotient.mk v.prime
  let j := algebraMap (ZMod p) (Zbar ⧸ v.prime)
  have hDz : (D : ZMod p) ≠ 0 := by rwa [ne_eq, ZMod.intCast_zmod_eq_zero_iff_dvd]
  obtain ⟨a, ha⟩ := (legendreSym.eq_one_iff p hDz).mp hsplit
  have ha' : a ^ 2 = (D : ZMod p) := by simpa only [pow_two] using ha.symm
  have ha0 : a ≠ 0 := fun h => hDz (by simp [← ha', h])
  have hs' : (q s) ^ 2 = (j a) ^ 2 := by
    rw [← q.map_pow, hs, ← j.map_pow, ha', map_intCast, map_intCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs' with h | h
  · exact ⟨a, ha0, ha', h.symm⟩
  · exact ⟨-a, neg_ne_zero.mpr ha0, (neg_sq a).trans ha', (j.map_neg a).trans h.symm⟩


end ZInQ.Manuscript.RC.WitnessSpec.FrobeniusPlace
