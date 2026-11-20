import ZInQKernel.Contrib.OneProof.RC.EvenMoving.Affine

/-! Matrix identities for tex 9503–9508 and 9519–9539. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenMoving

open Matrix Matrix.SpecialLinearGroup ModularGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

theorem det_eq (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  simpa only [Matrix.det_fin_two] using γ.det_coe

theorem sl_coord (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℤ) * (z : ℂ) + (γ 0 1 : ℤ)) /
      ((γ 1 0 : ℤ) * (z : ℂ) + (γ 1 1 : ℤ)) := by
  rw [coe_specialLinearGroup_apply]
  simp

theorem mem_level_iff {m : ℕ} (γ : SL(2, ℤ)) :
    γ ∈ Gamma0 m ↔ (m : ℤ) ∣ γ 1 0 := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Positive integral dilation of the argument. -/
def scalePoint (p : ℕ) (hp : 0 < p) : ℍ → ℍ :=
  affinePoint (p : ℚ) 0 (by exact_mod_cast hp)

theorem scalePoint_coe (p : ℕ) (hp : 0 < p) (z : ℍ) :
    (scalePoint p hp z : ℂ) = (p : ℂ) * (z : ℂ) := by
  simp [scalePoint, affinePoint_coe]

/-- The conjugate by `diag(p,1)`, integral when `p ∣ c`. -/
def scaleLower (p : ℕ) (γ : SL(2, ℤ)) (hc : (p : ℤ) ∣ γ 1 0) : SL(2, ℤ) :=
  ⟨!![γ 0 0, (p : ℤ) * γ 0 1; γ 1 0 / p, γ 1 1], by
    rw [Matrix.det_fin_two]
    change γ 0 0 * γ 1 1 - ((p : ℤ) * γ 0 1) * (γ 1 0 / p) = 1
    have h := Int.ediv_mul_cancel hc
    calc
      _ = γ 0 0 * γ 1 1 - γ 0 1 * ((γ 1 0 / p) * p) := by ring
      _ = γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 := congrArg (fun c => γ 0 0 * γ 1 1 - γ 0 1 * c) h
      _ = 1 := det_eq γ⟩

theorem scaleLower_entries (p : ℕ) (γ : SL(2, ℤ)) (hc : (p : ℤ) ∣ γ 1 0) :
    scaleLower p γ hc 0 0 = γ 0 0 ∧
    scaleLower p γ hc 0 1 = p * γ 0 1 ∧
    (p : ℤ) * scaleLower p γ hc 1 0 = γ 1 0 ∧
    scaleLower p γ hc 1 1 = γ 1 1 :=
  ⟨rfl, rfl, by
    change (p : ℤ) * (γ 1 0 / p) = γ 1 0
    rw [mul_comm, Int.ediv_mul_cancel hc], rfl⟩

/-- Read the conjugation in the holomorphic action. -/
theorem scale_smul (p : ℕ) (hp : 0 < p) (γ δ : SL(2, ℤ))
    (ha : δ 0 0 = γ 0 0) (hb : δ 0 1 = (p : ℤ) * γ 0 1)
    (hc : (p : ℤ) * δ 1 0 = γ 1 0) (hd : δ 1 1 = γ 1 1) (z : ℍ) :
    δ • scalePoint p hp z = scalePoint p hp (γ • z) := by
  apply UpperHalfPlane.ext
  rw [sl_coord δ, scalePoint_coe, scalePoint_coe, sl_coord γ, ha, hb, ← hc, hd]
  push_cast
  ring

/-- Right multiplication by `T^r` shifts the second column by `r` times the first. -/
theorem rightT_entries (γ : SL(2, ℤ)) (r : ℤ) :
    (γ * T ^ r) 0 0 = γ 0 0 ∧
    (γ * T ^ r) 0 1 = γ 0 1 + γ 0 0 * r ∧
    (γ * T ^ r) 1 0 = γ 1 0 ∧
    (γ * T ^ r) 1 1 = γ 1 1 + γ 1 0 * r := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    ModularGroup.coe_T_zpow, add_comm]

/-- Left multiplication by `T^r` shifts the top row by `r` times the bottom row. -/
theorem leftT_entries (γ : SL(2, ℤ)) (r : ℤ) :
    (T ^ r * γ) 0 0 = γ 0 0 + r * γ 1 0 ∧
    (T ^ r * γ) 0 1 = γ 0 1 + r * γ 1 1 ∧
    (T ^ r * γ) 1 0 = γ 1 0 ∧
    (T ^ r * γ) 1 1 = γ 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    ModularGroup.coe_T_zpow]

end ZInQ.Manuscript.RC.EvenMoving
