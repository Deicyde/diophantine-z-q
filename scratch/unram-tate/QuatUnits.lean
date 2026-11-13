import ZInQKernel.HDecomp.Descent.ProjRep

/-!
# unram-tate: matrix units from a quaternion action `i² = 2`, `j² = -3`, `ij = -ji`

Glue step (iii) of the bridge `TateBridge` (docs/research/g0-mod-field.md §3): the matrix units
of `B ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)`, for `B = (2, -3)_ℚ` (the kernel's `LeafQM.B`), acting on a vector space.
Over a field `E` with `2, 3 ≠ 0` and `s² = 2`: `X = s⁻¹ I`, `e₀₀ = (1+X)/2`, `e₁₁ = (1-X)/2`,
`e₀₁ = e₀₀ J`, `e₁₀ = -(1/3) J e₀₀`. Every operator commuting with `I` and `J` commutes with
every `e_{ij}`.
-/

namespace UnramTate

open GlueDescent

variable {E V : Type*} [Field E] [AddCommGroup V] [Module E V]

/-- Normal-form rewriting for words in `P`, `J` with `P² = P`, `PJ = J - JP`, `J² = -3`. -/
theorem quat_words (P J : Module.End E V) (hPP : P * P = P) (hPJ : P * J = J - J * P)
    (hJJ : J * J = (-3 : E) • (1 : Module.End E V)) :
    (∀ X, P * (P * X) = P * X) ∧ (∀ X, P * (J * X) = J * X - J * (P * X)) ∧
      (∀ X, J * (J * X) = (-3 : E) • X) := by
  refine ⟨fun X => by rw [← mul_assoc, hPP], fun X => by rw [← mul_assoc, hPJ, sub_mul, mul_assoc],
    fun X => by rw [← mul_assoc, hJJ, smul_mul_assoc, one_mul]⟩

theorem matrixUnits_of_quat (s : E) (hs : s ^ 2 = 2) (h2 : (2 : E) ≠ 0) (h3 : (3 : E) ≠ 0)
    (I J : Module.End E V) (hI : I * I = (2 : E) • (1 : Module.End E V))
    (hJ : J * J = (-3 : E) • (1 : Module.End E V)) (hIJ : I * J = -(J * I)) :
    ∃ u : MatrixUnits2 E V, ∀ (i j : Fin 2) (T : Module.End E V), Commute T I → Commute T J →
      Commute T (u.e i j) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs; exact h2 hs.symm
  set X : Module.End E V := s⁻¹ • I with hXdef
  have hXX : X * X = 1 := by
    rw [hXdef, smul_mul_smul_comm, hI, smul_smul]
    have : s⁻¹ * s⁻¹ * 2 = 1 := by rw [← hs]; field_simp
    rw [this, one_smul]
  have hXJ : X * J = -(J * X) := by
    rw [hXdef, smul_mul_assoc, hIJ, mul_smul_comm, smul_neg]
  set P : Module.End E V := (2 : E)⁻¹ • (1 + X) with hPdef
  have hPP : P * P = P := by
    rw [hPdef, smul_mul_smul_comm, add_mul, one_mul, mul_add, mul_one, hXX]
    rw [show (1 + X + (X + 1) : Module.End E V) = (2 : E) • (1 + X) by
      rw [two_smul]; abel, smul_smul]
    congr 1; field_simp
  have hPJ : P * J = J - J * P := by
    rw [hPdef, smul_mul_assoc, mul_smul_comm, add_mul, one_mul, hXJ, mul_add, mul_one]
    have h12 : (1 : E) - 2⁻¹ = 2⁻¹ := by field_simp; norm_num
    rw [show J - (2 : E)⁻¹ • (J + J * X) = ((1 : E) - 2⁻¹) • J + (2 : E)⁻¹ • (-(J * X)) by module,
      h12, ← smul_add]
  obtain ⟨wPP, wPJ, wJJ⟩ := quat_words P J hPP hPJ hJ
  let c : E := -(3 : E)⁻¹
  let e : Fin 2 → Fin 2 → Module.End E V := fun i j =>
    if i = 0 then (if j = 0 then P else P * J) else (if j = 0 then c • (J * P) else 1 - P)
  have hc : c * (-3 : E) = 1 := by simp only [c]; field_simp
  refine ⟨⟨e, ?_, ?_⟩, ?_⟩
  · intro i j k l
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp only [e, Fin.zero_eta, Fin.mk_one, Fin.isValue, ite_true, one_ne_zero, zero_ne_one,
        ite_false, mul_assoc, mul_sub, sub_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm,
        wPP, wPJ, wJJ, hPP, hPJ, hJ, smul_smul, smul_sub, sub_self, hc, one_smul, mul_zero,
        smul_zero, sub_zero, zero_sub, add_zero, zero_add, neg_zero] <;>
      first | rfl | abel | (simp only [sub_sub_cancel, sub_self, smul_zero]) | skip
  · show P + (1 - P) = 1
    abel
  · intro i j T hTI hTJ
    have hTX : Commute T X := hTI.smul_right _
    have hTP : Commute T P := ((Commute.one_right T).add_right hTX).smul_right _
    fin_cases i <;> fin_cases j
    · exact hTP
    · exact hTP.mul_right hTJ
    · exact (hTJ.mul_right hTP).smul_right _
    · exact (Commute.one_right T).sub_right hTP

end UnramTate

#print axioms UnramTate.matrixUnits_of_quat
