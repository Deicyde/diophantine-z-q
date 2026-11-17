import Mathlib.FieldTheory.IntermediateField.Basic
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.FiniteLinearDescent
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Coefficient-field coordinates for modular forms

An existing finite complex-linear representation descends to an intermediate
field when the represented form and every member of the family have all their
Fourier coefficients in that field. The linear system uses every natural-number
coefficient row simultaneously; no truncation or independence hypothesis is
needed. The result descends a given representation and does not assert spanning.
-/

set_option autoImplicit false

open scoped BigOperators Matrix MatrixGroups

namespace ModularFormCoefficientCoordinates

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
variable {h : ℝ} {k : ℤ} {J : Type*} [Fintype J]

/-- Taking a Fourier coefficient commutes with a finite complex-linear
combination of actual modular forms. -/
theorem coeff_sum_smul
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (F : J → _root_.ModularForm Γ k) (c : J → ℂ) (n : ℕ) :
    (UpperHalfPlane.qExpansion h (∑ j, c j • F j : _root_.ModularForm Γ k)).coeff n =
      ∑ j, c j * (UpperHalfPlane.qExpansion h (F j)).coeff n := by
  classical
  let e : _root_.ModularForm Γ k →ₗ[ℂ] ℂ :=
    (PowerSeries.coeff n).comp (TauCeti.ModularForm.qExpansionLinearMap hh hΓ k)
  change e (∑ j, c j • F j) = ∑ j, c j * e (F j)
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

/-- An actual finite complex-linear representation of a modular form whose
coefficients lie in an intermediate field has coordinates in that field, if the
same coefficient condition holds for every member of the representing family. -/
theorem exists_coordinates
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (K : IntermediateField ℚ ℂ)
    (F : J → _root_.ModularForm Γ k)
    (hF : ∀ j n, (UpperHalfPlane.qExpansion h (F j)).coeff n ∈ K)
    (g : _root_.ModularForm Γ k)
    (hg : ∀ n, (UpperHalfPlane.qExpansion h g).coeff n ∈ K)
    (c : J → ℂ) (hc : g = ∑ j, c j • F j) :
    ∃ d : J → K, g = ∑ j, (d j : ℂ) • F j := by
  classical
  let φ : K →+* ℂ := algebraMap K ℂ
  let A : Matrix ℕ J K := Matrix.of fun n j =>
    ⟨(UpperHalfPlane.qExpansion h (F j)).coeff n, hF j n⟩
  let b : ℕ → K := fun n =>
    ⟨(UpperHalfPlane.qExpansion h g).coeff n, hg n⟩
  have hcA : A.map φ *ᵥ c = φ ∘ b := by
    funext n
    change (∑ j, (UpperHalfPlane.qExpansion h (F j)).coeff n * c j) =
      (UpperHalfPlane.qExpansion h g).coeff n
    rw [hc, coeff_sum_smul hh hΓ F c n]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  obtain ⟨d, hd⟩ :=
    FiniteLinearDescent.exists_solution_of_field_extension φ A b hcA
  refine ⟨d, ?_⟩
  apply _root_.ModularForm.qExpansion_injective hh hΓ
  apply PowerSeries.ext
  intro n
  rw [coeff_sum_smul hh hΓ F (fun j => (d j : ℂ)) n]
  have hn : (∑ j, (UpperHalfPlane.qExpansion h (F j)).coeff n * (d j : ℂ)) =
      (UpperHalfPlane.qExpansion h g).coeff n := by
    have hnK := congrArg φ (congrFun hd n)
    simpa [Matrix.mulVec, dotProduct, A, b, φ, map_sum, map_mul] using hnK
  exact hn.symm.trans (Finset.sum_congr rfl fun j _ => mul_comm _ _)

end ModularFormCoefficientCoordinates
