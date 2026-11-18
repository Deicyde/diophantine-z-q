import ZInQKernel.Contrib.OneProof.RC.LineIndex.LocalPrincipal

/-!
# The right cosets in the good-prime Hecke double coset
Tex 8480–8487 and 9040–9042. The matrix factorization is on-the-spot (c).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Adelic

open Eichler LineIndex Matrix

private theorem matrix_on_line {K : Type*} [Field K] (A : Mat K) (hA : A.det = 0) :
    ∃ L : Option K, A ∈ columns (line L) := by
  rw [Matrix.det_fin_two, sub_eq_zero] at hA
  by_cases h : A 0 0 = 0
  · by_cases h' : A 0 1 = 0
    · exact ⟨none, fun j => (mem_line_iff _ _).mpr (by fin_cases j <;> assumption)⟩
    · have h10 : A 1 0 = 0 := (mul_eq_zero.mp (by simpa [h] using hA.symm)).resolve_left h'
      refine ⟨some (A 1 1 / A 0 1), fun j => (mem_line_iff _ _).mpr ?_⟩
      fin_cases j
      · simp [h, h10]
      · exact (div_mul_cancel₀ _ h').symm
  · refine ⟨some (A 1 0 / A 0 0), fun j => (mem_line_iff _ _).mpr ?_⟩
    fin_cases j
    · exact (div_mul_cancel₀ _ h).symm
    · change A 1 1 = A 1 0 / A 0 0 * A 0 1
      rw [div_mul_eq_mul_div, eq_div_iff h]
      simpa only [mul_comm] using hA

variable {p : ℕ} [Fact p.Prime]

theorem basis_in_hecke_double (L : Option (ZMod p)) :
    ∃ u v : (Mat ℤ_[p])ˣ, basisMatrix p L = (u : Mat ℤ_[p]) * basisMatrix p none * (v : Mat ℤ_[p]) := by
  cases L with
  | none => exact ⟨1, 1, by simp⟩
  | some t =>
    let A : Mat ℤ_[p] := !![0, 1; 1, (t.val : ℤ_[p])]
    let B : Mat ℤ_[p] := !![0, 1; 1, 0]
    have hA : IsUnit A := by
      rw [Matrix.isUnit_iff_isUnit_det]
      simp [A, Matrix.det_fin_two_of]
    have hB : IsUnit B := by
      rw [Matrix.isUnit_iff_isUnit_det]
      simp [B, Matrix.det_fin_two_of]
    refine ⟨hA.unit, hB.unit, ?_⟩
    rw [hA.unit_spec, hB.unit_spec]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [basisMatrix, A, B, Matrix.mul_apply, Fin.sum_univ_two]

private theorem basis_right_distinct (L M : Option (ZMod p)) (v : (Mat ℤ_[p])ˣ)
    (h : basisMatrix p L = basisMatrix p M * (v : Mat ℤ_[p])) : L = M := by
  have hcol : reduce p (basisMatrix p L) ∈ columns (line M) :=
    (reduce_mem_columns_iff M _).mpr ⟨v, h⟩
  have hvec : lineVector L ∈ line M := by
    cases L with
    | none =>
      have hh := hcol (1 : Fin 2)
      convert hh using 1
      ext i; fin_cases i <;> simp [basisMatrix, lineVector, reduce]
    | some t =>
      have hh := hcol (0 : Fin 2)
      convert hh using 1
      ext i; fin_cases i <;> simp [basisMatrix, lineVector, reduce]
  have hle : line L ≤ line M := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvec)
  apply (lines (K := ZMod p)).injective
  apply Subtype.ext
  exact Submodule.eq_of_le_of_finrank_le hle (by rw [(lines (K := ZMod p) L).prop,
    (lines (K := ZMod p) M).prop])

/-- The good-prime double coset of diag(p,1), cut into its p+1 right cosets
with the representatives used by the ideal line indexing. -/
theorem hecke_matrix_cosets (A : Mat ℤ_[p]) :
    (∃ u v : (Mat ℤ_[p])ˣ, A = (u : Mat ℤ_[p]) * basisMatrix p none * (v : Mat ℤ_[p])) ↔
      ∃! L : Option (ZMod p), ∃ v : (Mat ℤ_[p])ˣ, A = basisMatrix p L * (v : Mat ℤ_[p]) := by
  constructor
  · rintro ⟨u, v, rfl⟩
    let A := (u : Mat ℤ_[p]) * basisMatrix p none * (v : Mat ℤ_[p])
    have hdet : (reduce p A).det = 0 := by
      rw [reduce, ← RingHom.map_det]
      simp [A, Matrix.det_mul, basisMatrix_det]
    obtain ⟨L, hL⟩ := matrix_on_line _ hdet
    obtain ⟨B, hB⟩ := (reduce_mem_columns_iff L A).mp hL
    have hBdet : B.det = (u : Mat ℤ_[p]).det * (v : Mat ℤ_[p]).det := by
      have he := congrArg Matrix.det hB
      change ((u : Mat ℤ_[p]) * basisMatrix p none * (v : Mat ℤ_[p])).det = _ at he
      simp only [Matrix.det_mul, basisMatrix_det] at he
      apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero : (p : ℤ_[p]) ≠ 0)
      calc
        _ = (u : Mat ℤ_[p]).det * p * (v : Mat ℤ_[p]).det := he.symm
        _ = _ := by ring
    have hu : IsUnit B := by
      rw [Matrix.isUnit_iff_isUnit_det, hBdet]
      exact (Matrix.isUnits_det_units u).mul (Matrix.isUnits_det_units v)
    refine ⟨L, ⟨hu.unit, by rw [hu.unit_spec]; exact hB⟩, ?_⟩
    rintro M ⟨w, hw⟩
    apply basis_right_distinct M L (hu.unit * w⁻¹)
    have he := hw.symm.trans hB
    rw [← hu.unit_spec] at he
    change basisMatrix p M * (w : Mat ℤ_[p]) =
      basisMatrix p L * (hu.unit : Mat ℤ_[p]) at he
    rw [Units.val_mul, ← mul_assoc, ← he, mul_assoc, Units.mul_inv, mul_one]
  · rintro ⟨L, ⟨w, hw⟩, -⟩
    obtain ⟨u, v, he⟩ := basis_in_hecke_double L
    exact ⟨u, v * w, by rw [hw, he, Units.val_mul, mul_assoc]⟩

#print axioms matrix_on_line
#print axioms basis_in_hecke_double
#print axioms basis_right_distinct
#print axioms hecke_matrix_cosets

end ZInQ.Manuscript.RC.Adelic
