import Mathlib.LinearAlgebra.Vandermonde
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# Homogeneous determinants of actual modular forms

A matrix whose column weights are fixed has a genuine determinant modular
form of the sum of those weights. Its Fourier expansion is the determinant
of the Fourier expansions. In particular, pairwise distinct expansions of
weight-one forms give a nonzero homogeneous Vandermonde form.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane
open scoped MatrixGroups ModularForm BigOperators

namespace DirectWeightedDeterminant

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]

/-- The genuine homogeneous determinant, assembled from finite products. -/
def determinantForm {n : ℕ} (w : Fin n → ℤ)
    (F : (i j : Fin n) → ModularForm Γ (w j)) : ModularForm Γ (∑ j, w j) :=
  ∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ •
    ModularForm.prod (∑ j, w j) rfl (fun j => F (σ j) j)

/-- Its pointwise value is the ordinary determinant of the actual values. -/
theorem determinantForm_apply {n : ℕ} (w : Fin n → ℤ)
    (F : (i j : Fin n) → ModularForm Γ (w j)) (τ : ℍ) :
    determinantForm w F τ = Matrix.det ((fun i j => F i j τ) : Matrix (Fin n) (Fin n) ℂ) := by
  simp [determinantForm, Matrix.det_apply, ModularForm.coe_prod, Units.smul_def]

/-- Row permutation changes this form by exactly the ordinary determinant sign. -/
theorem determinantForm_row_permute {n : ℕ} (w : Fin n → ℤ)
    (F : (i j : Fin n) → ModularForm Γ (w j)) (σ : Equiv.Perm (Fin n)) :
    determinantForm w (fun i j => F (σ i) j) =
      Equiv.Perm.sign σ • determinantForm w F := by
  ext τ
  rw [determinantForm_apply]
  change Matrix.det ((fun i j => F (σ i) j τ) : Matrix (Fin n) (Fin n) ℂ) =
    Equiv.Perm.sign σ • (determinantForm w F τ)
  rw [determinantForm_apply]
  let M : Matrix (Fin n) (Fin n) ℂ := fun i j => F i j τ
  have h := Matrix.det_permute σ M
  have hm : M.submatrix σ id = (fun i j => F (σ i) j τ) := by
    funext i j
    simp only [Matrix.submatrix_apply, id_eq, M]
  rw [hm] at h
  simpa only [M, Units.smul_def, zsmul_eq_mul] using h

/-- Fourier expansion commutes with a finite product even when the weights vary. -/
theorem qExpansion_weighted_product {ι : Type*} (s : Finset ι) (w : ι → ℤ)
    (F : (i : ι) → ModularForm Γ (w i)) {h : ℝ}
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    qExpansion h (fun τ : ℍ => ∏ i ∈ s, F i τ) = ∏ i ∈ s, qExpansion h (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty]
      exact UpperHalfPlane.qExpansion_one h
  | @insert a s ha hs =>
      have hp : (fun τ : ℍ => ∏ i ∈ s, F i τ) =
          ⇑(ModularForm.prod (∑ i ∈ s, w i) rfl F) := by
        funext τ
        simp only [ModularForm.coe_prod, Finset.prod_apply]
      have hprod : (fun τ : ℍ => ∏ i ∈ insert a s, F i τ) =
          ⇑(F a) * ⇑(ModularForm.prod (∑ i ∈ s, w i) rfl F) := by
        funext τ
        simp only [Finset.prod_insert ha, Pi.mul_apply, ModularForm.coe_prod, Finset.prod_apply]
      rw [hprod, ModularForm.qExpansion_mul_coe hh hΓ (F a)
        (ModularForm.prod (∑ i ∈ s, w i) rfl F), ← hp, hs, Finset.prod_insert ha]

/-- The Fourier expansion of the actual determinant form is the ordinary formal determinant. -/
theorem qExpansion_determinantForm {n : ℕ} (w : Fin n → ℤ)
    (F : (i j : Fin n) → ModularForm Γ (w j)) {h : ℝ}
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    qExpansion h (determinantForm w F) =
      Matrix.det ((fun i j => qExpansion h (F i j)) : Matrix (Fin n) (Fin n) (PowerSeries ℂ)) := by
  let qL := TauCeti.ModularForm.qExpansionLinearMap hh hΓ (∑ j, w j)
  change qL (determinantForm w F) = _
  rw [determinantForm, map_sum, Matrix.det_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Units.smul_def, map_zsmul, Units.smul_def]
  congr 1
  rw [TauCeti.ModularForm.qExpansionLinearMap_apply]
  have he : ⇑(ModularForm.prod (∑ j, w j) rfl (fun j => F (σ j) j)) =
      (fun τ : ℍ => ∏ j : Fin n, F (σ j) j τ) := by
    funext τ
    simp only [ModularForm.coe_prod, Finset.prod_apply]
  rw [he]
  exact qExpansion_weighted_product Finset.univ w (fun j => F (σ j) j) hh hΓ

/-- The actual homogeneous Vandermonde form in weight-one modular forms. -/
def vandermondeForm {n : ℕ} (F : Fin n → ModularForm Γ 1) :
    ModularForm Γ (∑ j : Fin n, (j : ℤ)) :=
  determinantForm (fun j => (j : ℤ))
    (fun i j => ModularForm.mcast (by ring) ((F i).pow (j : ℕ)))

/-- Its exact analytic value, with the original forms and ordinary Vandermonde matrix. -/
theorem vandermondeForm_apply {n : ℕ} (F : Fin n → ModularForm Γ 1) (τ : ℍ) :
    vandermondeForm F τ = (Matrix.vandermonde (fun i => F i τ)).det := by
  rw [vandermondeForm, determinantForm_apply]
  congr 1
  ext i j
  simp [Matrix.vandermonde_apply]

/-- The actual principal-period expansion is the Vandermonde determinant of the expansions. -/
theorem qExpansion_vandermondeForm {n : ℕ} (F : Fin n → ModularForm Γ 1) {h : ℝ}
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods) :
    qExpansion h (vandermondeForm F) =
      (Matrix.vandermonde (fun i => qExpansion h (F i))).det := by
  rw [vandermondeForm, qExpansion_determinantForm _ _ hh hΓ]
  congr 1
  funext i j
  simp only [Matrix.vandermonde_apply, ModularForm.coe_mcast]
  exact ModularForm.qExpansion_pow hh hΓ (F i) (j : ℕ)

/-- Pairwise distinct actual expansions force this homogeneous form to be nonzero. -/
theorem vandermondeForm_ne_zero {n : ℕ} (F : Fin n → ModularForm Γ 1) {h : ℝ}
    (hh : 0 < h) (hΓ : h ∈ Γ.strictPeriods)
    (hF : Function.Injective (fun i => qExpansion h (F i))) :
    vandermondeForm F ≠ 0 := by
  have hq : qExpansion h (vandermondeForm F) ≠ 0 := by
    rw [qExpansion_vandermondeForm F hh hΓ, Matrix.det_vandermonde]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hji : i < j := Finset.mem_Ioi.mp hj
    exact sub_ne_zero.mpr (fun he => (ne_of_gt hji) (hF he))
  intro hz
  apply hq
  rw [hz]
  exact (TauCeti.ModularForm.qExpansionLinearMap hh hΓ (∑ j : Fin n, (j : ℤ))).map_zero

end DirectWeightedDeterminant
