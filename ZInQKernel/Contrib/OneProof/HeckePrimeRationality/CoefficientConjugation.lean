import Mathlib.Algebra.Algebra.Equiv
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoefficientCoordinates

/-!
# Coefficient conjugation from a finite family

An automorphism of the coefficient field transports a given finite representation
when explicit conjugate forms are supplied for its family. The construction acts
on field-valued coordinates and Fourier coefficients, not on complex values of
modular forms. Equality of all Fourier coefficients gives uniqueness. Rational
coefficients are fixed by every automorphism over the rational numbers.
-/

set_option autoImplicit false

open scoped BigOperators MatrixGroups

namespace ModularFormCoefficientConjugation

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
variable {h : ℝ} {k : ℤ} {J : Type*} [Fintype J]

/-- A finite representation admits field-valued coordinates whose images give
an explicit form with the conjugated Fourier coefficients. -/
theorem exists_coordinates_conjugate
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (K : IntermediateField ℚ ℂ)
    (F G : J → _root_.ModularForm Γ k)
    (hF : ∀ j n, (UpperHalfPlane.qExpansion h (F j)).coeff n ∈ K)
    (σ : K ≃ₐ[ℚ] K)
    (hG : ∀ j n, (UpperHalfPlane.qExpansion h (G j)).coeff n =
      (σ (⟨(UpperHalfPlane.qExpansion h (F j)).coeff n, hF j n⟩ : K) : ℂ))
    (g : _root_.ModularForm Γ k)
    (hg : ∀ n, (UpperHalfPlane.qExpansion h g).coeff n ∈ K)
    (c : J → ℂ) (hc : g = ∑ j, c j • F j) :
    ∃ d : J → K, g = ∑ j, (d j : ℂ) • F j ∧
      ∀ n, (UpperHalfPlane.qExpansion h
        (∑ j, (σ (d j) : ℂ) • G j : _root_.ModularForm Γ k)).coeff n =
        (σ (⟨(UpperHalfPlane.qExpansion h g).coeff n, hg n⟩ : K) : ℂ) := by
  classical
  obtain ⟨d, hd⟩ :=
    ModularFormCoefficientCoordinates.exists_coordinates hh hΓ K F hF g hg c hc
  let φ : K →+* ℂ := algebraMap K ℂ
  have hcoeffK (n : ℕ) :
      (⟨(UpperHalfPlane.qExpansion h g).coeff n, hg n⟩ : K) =
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
  refine ⟨d, hd, ?_⟩
  intro n
  have hmap := congrArg (fun z : K => φ (σ z)) (hcoeffK n)
  simp only [map_sum, map_mul] at hmap
  rw [ModularFormCoefficientCoordinates.coeff_sum_smul hh hΓ G
    (fun j => (σ (d j) : ℂ)) n]
  simpa only [hG, φ, IntermediateField.algebraMap_apply] using hmap.symm

/-- Explicit coefficient-conjugate family data yields a unique actual modular
form with the conjugated Fourier coefficients of the represented form. -/
theorem exists_unique_conjugate
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (K : IntermediateField ℚ ℂ)
    (F G : J → _root_.ModularForm Γ k)
    (hF : ∀ j n, (UpperHalfPlane.qExpansion h (F j)).coeff n ∈ K)
    (σ : K ≃ₐ[ℚ] K)
    (hG : ∀ j n, (UpperHalfPlane.qExpansion h (G j)).coeff n =
      (σ (⟨(UpperHalfPlane.qExpansion h (F j)).coeff n, hF j n⟩ : K) : ℂ))
    (g : _root_.ModularForm Γ k)
    (hg : ∀ n, (UpperHalfPlane.qExpansion h g).coeff n ∈ K)
    (c : J → ℂ) (hc : g = ∑ j, c j • F j) :
    ∃! gσ : _root_.ModularForm Γ k,
      ∀ n, (UpperHalfPlane.qExpansion h gσ).coeff n =
        (σ (⟨(UpperHalfPlane.qExpansion h g).coeff n, hg n⟩ : K) : ℂ) := by
  classical
  obtain ⟨d, hd, hcoeff⟩ :=
    exists_coordinates_conjugate hh hΓ K F G hF σ hG g hg c hc
  refine ⟨(∑ j, (σ (d j) : ℂ) • G j : _root_.ModularForm Γ k), hcoeff, ?_⟩
  intro g' hg'
  apply _root_.ModularForm.qExpansion_injective hh hΓ
  apply PowerSeries.ext
  intro n
  exact (hg' n).trans (hcoeff n).symm

omit [Γ.HasDetOne] in
/-- A form with rational Fourier coefficients is fixed by coefficient
conjugation over the rational numbers. No automorphism of the complex numbers
is used. -/
theorem conjugate_eq_of_rational_coefficients
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (K : IntermediateField ℚ ℂ) (σ : K ≃ₐ[ℚ] K)
    (g gσ : _root_.ModularForm Γ k)
    (hg : ∀ n, (UpperHalfPlane.qExpansion h g).coeff n ∈ K)
    (hσ : ∀ n, (UpperHalfPlane.qExpansion h gσ).coeff n =
      (σ (⟨(UpperHalfPlane.qExpansion h g).coeff n, hg n⟩ : K) : ℂ))
    (hQ : ∀ n, ∃ q : ℚ, (UpperHalfPlane.qExpansion h g).coeff n = (q : ℂ)) :
    gσ = g := by
  apply _root_.ModularForm.qExpansion_injective hh hΓ
  apply PowerSeries.ext
  intro n
  obtain ⟨q, hq⟩ := hQ n
  have hqmap := (Rat.castHom ℂ).map_rat_algebraMap q
  change (q : ℂ) = algebraMap ℚ ℂ q at hqmap
  have hqA : (UpperHalfPlane.qExpansion h g).coeff n = algebraMap ℚ ℂ q :=
    hq.trans hqmap
  have hb : (⟨(UpperHalfPlane.qExpansion h g).coeff n, hg n⟩ : K) =
      algebraMap ℚ K q := by
    apply Subtype.ext
    simpa only [IntermediateField.coe_algebraMap_apply] using hqA
  rw [hσ n, hb, σ.commutes]
  simpa only [IntermediateField.coe_algebraMap_apply] using hqA.symm

end ModularFormCoefficientConjugation
