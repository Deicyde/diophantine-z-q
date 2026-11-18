import ZInQKernel.Contrib.OneProof.RC.O12Local.Conductor

/-! The change from Casselman's upper-left convention to the manuscript's
lower-right convention (tex 9819–9824). The conjugation works at all levels
in the dimension formula, with the manuscript's (h_p) at level one. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Local

open Matrix

variable (p : ℕ) [Fact p.Prime]

/-- The lower-left congruence group (K_0(p^n)), expressed as an entry test. -/
def atK0 (n : ℕ) (g : GL (Fin 2) ℚ_[p]) : Prop :=
  let A : Matrix (Fin 2) (Fin 2) ℚ_[p] := g
  (∀ i j, ‖A i j‖ ≤ 1) ∧ ‖A.det‖ = 1 ∧ ‖A 1 0‖ ≤ ((p : ℝ)⁻¹)^n

/-- The conjugating matrix for the two conventions. -/
def switchMatrix (n : ℕ) : GL (Fin 2) ℚ_[p] :=
  GeneralLinearGroup.mkOfDetNeZero !![0, 1; -(p : ℚ_[p])^n, 0] (by
    have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    simpa [det_fin_two] using pow_ne_zero n hp)

theorem switchMatrix_conjugation (n : ℕ) (g : GL (Fin 2) ℚ_[p]) :
    let A : Matrix (Fin 2) (Fin 2) ℚ_[p] := g
    (↑(switchMatrix p n * g * (switchMatrix p n)⁻¹) : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
      !![A 1 1, -A 1 0 / (p : ℚ_[p])^n; -(p : ℚ_[p])^n * A 0 1, A 0 0] := by
  dsimp only
  let H := switchMatrix p n
  let A : Matrix (Fin 2) (Fin 2) ℚ_[p] := g
  let M : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
    !![A 1 1, -A 1 0 / (p : ℚ_[p])^n; -(p : ℚ_[p])^n * A 0 1, A 0 0]
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hmul : (H : Matrix (Fin 2) (Fin 2) ℚ_[p]) * A = M * (H : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [H, switchMatrix, M, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals field_simp [hp]
  change ((H : Matrix (Fin 2) (Fin 2) ℚ_[p]) * A) *
    ((H⁻¹ : GL (Fin 2) ℚ_[p]) : Matrix (Fin 2) (Fin 2) ℚ_[p]) = M
  rw [hmul, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

/-- Conjugation preserves (K_0(p^n)) and swaps its diagonal entries.
In particular the upper-left character pulls back to the lower-right one. -/
theorem switchMatrix_atK0 (n : ℕ) (g : GL (Fin 2) ℚ_[p]) :
    atK0 p n (switchMatrix p n * g * (switchMatrix p n)⁻¹) ↔ atK0 p n g := by
  let A : Matrix (Fin 2) (Fin 2) ℚ_[p] := g
  let M : Matrix (Fin 2) (Fin 2) ℚ_[p] :=
    !![A 1 1, -A 1 0 / (p : ℚ_[p])^n; -(p : ℚ_[p])^n * A 0 1, A 0 0]
  unfold atK0
  rw [switchMatrix_conjugation]
  change ((∀ i j, ‖M i j‖ ≤ 1) ∧ ‖M.det‖ = 1 ∧ ‖M 1 0‖ ≤ _) ↔
    ((∀ i j, ‖A i j‖ ≤ 1) ∧ ‖A.det‖ = 1 ∧ ‖A 1 0‖ ≤ _)
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hnorm : ‖(p : ℚ_[p])^n‖ = ((p : ℝ)⁻¹)^n := by rw [norm_pow, Padic.norm_p]
  have hpos : 0 < ((p : ℝ)⁻¹)^n := hnorm ▸ norm_pos_iff.mpr (pow_ne_zero _ hp)
  have hle : ((p : ℝ)⁻¹)^n ≤ 1 :=
    pow_le_one₀ (inv_nonneg.mpr (Nat.cast_nonneg _)) (inv_le_one_of_one_le₀ (by
      exact_mod_cast (Fact.out : p.Prime).one_le))
  have hdet : M.det = A.det := by
    simp [M, det_fin_two]
    field_simp [hp]
    ring
  have h₀₁ : ‖M 0 1‖ ≤ 1 ↔ ‖A 1 0‖ ≤ ((p : ℝ)⁻¹)^n := by
    change ‖-A 1 0 / (p : ℚ_[p])^n‖ ≤ 1 ↔ _
    rw [norm_div, norm_neg, hnorm, div_le_one hpos]
  have h₁₀ : ‖M 1 0‖ ≤ ((p : ℝ)⁻¹)^n ↔ ‖A 0 1‖ ≤ 1 := by
    change ‖-(p : ℚ_[p])^n * A 0 1‖ ≤ _ ↔ _
    rw [norm_mul, norm_neg, hnorm]
    constructor
    · intro h
      apply (mul_le_mul_iff_of_pos_left hpos).mp
      simpa only [mul_one] using h
    · intro h
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h hpos.le
  rw [hdet, h₁₀]
  constructor
  · rintro ⟨hi, hd, hb⟩
    refine ⟨?_, hd, h₀₁.mp (hi 0 1)⟩
    intro i j
    fin_cases i <;> fin_cases j
    · exact hi 1 1
    · exact hb
    · exact (h₀₁.mp (hi 0 1)).trans hle
    · exact hi 0 0
  · rintro ⟨hi, hd, hc⟩
    refine ⟨?_, hd, hi 0 1⟩
    intro i j
    fin_cases i <;> fin_cases j
    · exact hi 1 1
    · exact h₀₁.mpr hc
    · exact (h₁₀.mpr (hi 0 1)).trans hle
    · exact hi 0 0

/-- The same conjugation transports the lower-right (K_1) test to the
upper-left test at the level used for Casselman's fixed-space formula. -/
theorem switchMatrix_atK1 (n : ℕ) (g : GL (Fin 2) ℚ_[p]) :
    atK1 p n g ↔ atK0 p n (switchMatrix p n * g * (switchMatrix p n)⁻¹) ∧
      (n = 0 ∨
        ‖(↑(switchMatrix p n * g * (switchMatrix p n)⁻¹) : Matrix (Fin 2) (Fin 2) ℚ_[p])
          0 0 - 1‖ ≤ ((p : ℝ)⁻¹)^n) := by
  rw [switchMatrix_atK0, switchMatrix_conjugation]
  let A : Matrix (Fin 2) (Fin 2) ℚ_[p] := g
  let r := ((p : ℝ)⁻¹)^n
  change ((∀ i j, ‖A i j‖ ≤ 1) ∧ ‖A.det‖ = 1 ∧
    (n = 0 ∨ (‖A 1 0‖ ≤ r ∧ ‖A 1 1 - 1‖ ≤ r))) ↔
    (((∀ i j, ‖A i j‖ ≤ 1) ∧ ‖A.det‖ = 1 ∧ ‖A 1 0‖ ≤ r) ∧
      (n = 0 ∨ ‖A 1 1 - 1‖ ≤ r))
  constructor
  · rintro ⟨hint, hdet, hn | ⟨hc, hd⟩⟩
    · have hc : ‖A 1 0‖ ≤ r := by simpa [r, hn] using hint 1 0
      exact ⟨⟨hint, hdet, hc⟩, Or.inl hn⟩
    · exact ⟨⟨hint, hdet, hc⟩, Or.inr hd⟩
  · rintro ⟨⟨hint, hdet, hc⟩, hn | hd⟩
    · exact ⟨hint, hdet, Or.inl hn⟩
    · exact ⟨hint, hdet, Or.inr ⟨hc, hd⟩⟩

#print axioms switchMatrix_atK1
#print axioms switchMatrix_conjugation
#print axioms switchMatrix_atK0

end ZInQ.Manuscript.RC.O12Local
