import Mathlib.Algebra.Algebra.Equiv
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoefficientCoordinates

/-!
# Fourier coefficients with prescribed field coordinates

These lemmas use a given coordinate vector over an intermediate field. The same
vector controls every Fourier row, and its images control coefficient conjugation.
-/

set_option autoImplicit false
open scoped BigOperators MatrixGroups

namespace KnownFieldCoefficientCoordinates

/-- Rational complex numbers belong to every rational intermediate field. -/
theorem rational_mem (K : IntermediateField ℚ ℂ) (q : ℚ) : (q : ℂ) ∈ K := by
  have hq := (Rat.castHom ℂ).map_rat_algebraMap q
  change (q : ℂ) = algebraMap ℚ ℂ q at hq
  have hx : ((algebraMap ℚ K q : K) : ℂ) = (q : ℂ) := by
    rw [IntermediateField.coe_algebraMap_apply]
    exact hq.symm
  exact hx ▸ (algebraMap ℚ K q).property

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
variable {h : ℝ} {k : ℤ} {J : Type*} [Fintype J]

/-- A finite combination with field-valued coordinates has coefficients in the
same field whenever its family does. -/
theorem combination_coeff_mem
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (K : IntermediateField ℚ ℂ)
    (F : J → _root_.ModularForm Γ k)
    (hF : ∀ j n, (UpperHalfPlane.qExpansion h (F j)).coeff n ∈ K)
    (d : J → K) (n : ℕ) :
    (UpperHalfPlane.qExpansion h
      (∑ j, (d j : ℂ) • F j : _root_.ModularForm Γ k)).coeff n ∈ K := by
  classical
  let x : K := ∑ j, d j *
    (⟨(UpperHalfPlane.qExpansion h (F j)).coeff n, hF j n⟩ : K)
  have hx : (x : ℂ) = (UpperHalfPlane.qExpansion h
      (∑ j, (d j : ℂ) • F j : _root_.ModularForm Γ k)).coeff n := by
    change (algebraMap K ℂ) (∑ j, d j *
      (⟨(UpperHalfPlane.qExpansion h (F j)).coeff n, hF j n⟩ : K)) = _
    rw [map_sum, ModularFormCoefficientCoordinates.coeff_sum_smul hh hΓ F
      (fun j => (d j : ℂ)) n]
    simp only [map_mul, IntermediateField.algebraMap_apply]
  exact hx ▸ x.property

/-- Conjugation of a known field-coordinate representation uses that same
coordinate vector, without a second solvability choice. -/
theorem conjugate_coeff_of_known_coordinates
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) (K : IntermediateField ℚ ℂ)
    (F G : J → _root_.ModularForm Γ k)
    (hF : ∀ j n, (UpperHalfPlane.qExpansion h (F j)).coeff n ∈ K)
    (σ : K ≃ₐ[ℚ] K)
    (hG : ∀ j n, (UpperHalfPlane.qExpansion h (G j)).coeff n =
      (σ (⟨(UpperHalfPlane.qExpansion h (F j)).coeff n, hF j n⟩ : K) : ℂ))
    (g : _root_.ModularForm Γ k)
    (hg : ∀ n, (UpperHalfPlane.qExpansion h g).coeff n ∈ K)
    (d : J → K) (hd : g = ∑ j, (d j : ℂ) • F j) (n : ℕ) :
    (UpperHalfPlane.qExpansion h
      (∑ j, (σ (d j) : ℂ) • G j : _root_.ModularForm Γ k)).coeff n =
      (σ (⟨(UpperHalfPlane.qExpansion h g).coeff n, hg n⟩ : K) : ℂ) := by
  classical
  let φ : K →+* ℂ := algebraMap K ℂ
  have hcoeffK : (⟨(UpperHalfPlane.qExpansion h g).coeff n, hg n⟩ : K) =
      ∑ j, d j * (⟨(UpperHalfPlane.qExpansion h (F j)).coeff n, hF j n⟩ : K) := by
    apply Subtype.ext
    change φ (⟨(UpperHalfPlane.qExpansion h g).coeff n, hg n⟩ : K) =
      φ (∑ j, d j * (⟨(UpperHalfPlane.qExpansion h (F j)).coeff n, hF j n⟩ : K))
    rw [map_sum]
    simp only [map_mul]
    change (UpperHalfPlane.qExpansion h g).coeff n =
      ∑ j, (d j : ℂ) * (UpperHalfPlane.qExpansion h (F j)).coeff n
    rw [hd, ModularFormCoefficientCoordinates.coeff_sum_smul hh hΓ F
      (fun j => (d j : ℂ)) n]
  have hmap := congrArg (fun z : K => φ (σ z)) hcoeffK
  simp only [map_sum, map_mul] at hmap
  rw [ModularFormCoefficientCoordinates.coeff_sum_smul hh hΓ G
    (fun j => (σ (d j) : ℂ)) n]
  simpa only [hG, φ, IntermediateField.algebraMap_apply] using hmap.symm

end KnownFieldCoefficientCoordinates
