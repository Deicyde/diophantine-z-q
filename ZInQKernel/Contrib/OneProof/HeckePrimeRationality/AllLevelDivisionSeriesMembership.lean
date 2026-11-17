import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelEisensteinWeightTwoBounds
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionWeierstrassForms
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionMuFourierFinite
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionQuadraticCases

/-!
# Actual torsion forms in the independent division-series span

The generating forms are defined by convergent inverse-square congruence
lattice differences. Equality with the actual Weierstrass forms, finite
Fourier inversion, and the complete quadratic label cases give membership.
This span is not asserted to be the whole modular-form space or a
Petersson-defined Eisenstein subspace.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open Complex ModularForm
open scoped Real UpperHalfPlane Modular MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.DivisionSeriesMembership

open ZInQ.Contrib.HeckePrimeRationality

/-- The actual ambient space of weight-two principal-congruence modular forms. -/
abbrev WeightTwo (N : _root_.Nat) :=
  _root_.ModularForm ((_root_.CongruenceSubgroup.Gamma N).map
    (_root_.Matrix.SpecialLinearGroup.mapGL _root_.Real)) 2

/-- The span of independently series-defined division Eisenstein forms. -/
def divisionSpan (N : _root_.Nat) (hN : 0 < N) : _root_.Submodule _root_.Complex (WeightTwo N) :=
  Submodule.span ℂ (Set.range (fun p : ℤ × ℤ =>
    EisensteinWeightTwo.divisionEisensteinMF N hN ![p.1, p.2]))

/-- Each generator enters the span through its actual series-defined form. -/
theorem divisionEisensteinMF_mem (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int) :
    EisensteinWeightTwo.divisionEisensteinMF N hN ![a, b] ∈ divisionSpan N hN := by
  apply Submodule.subset_span
  exact ⟨(a, b), rfl⟩

/-- Equality of the actual Weierstrass form and the independent lattice-series form, on all labels. -/
theorem xForm_eq_divisionEisensteinMF (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int) :
    WeierstrassForms.xForm N hN a b = EisensteinWeightTwo.divisionEisensteinMF N hN ![a, b] := by
  apply DFunLike.ext
  intro τ
  rw [WeierstrassForms.xForm_apply, EisensteinWeightTwo.divisionEisensteinMF_eq_xValue_all]

/-- The actual x-form belongs to the independently generated series span. -/
theorem xForm_mem_divisionSpan (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int) :
    WeierstrassForms.xForm N hN a b ∈ divisionSpan N hN := by
  rw [xForm_eq_divisionEisensteinMF]
  exact divisionEisensteinMF_mem N hN a b

/-- The constant alternating character for a finite source label and an integer target label. -/
def coefficient (N : _root_.Nat) (a b : Fin N) (r s : _root_.Int) : _root_.Complex :=
  cexp (2 * (Real.pi : ℂ) * I *
    (((b : ℕ) : ℂ) * (r : ℂ) - ((a : ℕ) : ℂ) * (s : ℂ)) / (N : ℂ))

/-- Actual inverse Fourier duality as an equality of genuine modular forms. -/
theorem muForm_eq_series_combination (N : _root_.Nat) (hN : 0 < N) (r s : _root_.Int) :
    WeierstrassForms.muForm N hN r s =
      (-(1 / (N : ℂ) ^ 2)) •
        ∑ a : Fin N, ∑ b : Fin N, coefficient N a b r s •
          EisensteinWeightTwo.divisionEisensteinMF N hN ![(a : ℕ), (b : ℕ)] := by
  let _ : NeZero N := ⟨hN.ne'⟩
  apply DFunLike.ext
  intro τ
  simp only [WeierstrassForms.muForm_apply, _root_.smul_apply, _root_.sum_apply, smul_eq_mul,
    EisensteinWeightTwo.divisionEisensteinMF_eq_xValue_all]
  have h := TorsionMuFourier.mu_fourier_duality N τ r s
  simpa only [coefficient, mul_comm] using h

/-- The actual μ-form is a finite constant linear combination of the independent series forms. -/
theorem muForm_mem_divisionSpan (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int) :
    WeierstrassForms.muForm N hN a b ∈ divisionSpan N hN := by
  rw [muForm_eq_series_combination]
  apply (divisionSpan N hN).smul_mem
  apply (divisionSpan N hN).sum_mem
  intro r _
  apply (divisionSpan N hN).sum_mem
  intro s _
  exact (divisionSpan N hN).smul_mem _ (divisionEisensteinMF_mem N hN (r : ℕ) (s : ℕ))

/-- The genuine product of two weight-one torsion forms, placed in weight two. -/
def lambdaProductForm (N : _root_.Nat) (hN : 0 < N) (a b c d : _root_.Int) : WeightTwo N :=
  ModularForm.mcast (by norm_num)
    ((WeierstrassForms.lambdaForm N hN a b).mul (WeierstrassForms.lambdaForm N hN c d))

theorem lambdaProductForm_apply (N : _root_.Nat) (hN : 0 < N) (a b c d : _root_.Int)
    (τ : _root_.UpperHalfPlane) :
    lambdaProductForm N hN a b c d τ =
      TorsionWeierstrassData.lambdaValue N a b τ * TorsionWeierstrassData.lambdaValue N c d τ := by
  change WeierstrassForms.lambdaForm N hN a b τ * WeierstrassForms.lambdaForm N hN c d τ = _
  rw [WeierstrassForms.lambdaForm_apply, WeierstrassForms.lambdaForm_apply]

/-- The square of the actual weight-one torsion form. -/
def lambdaSquareForm (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int) : WeightTwo N :=
  lambdaProductForm N hN a b a b

theorem lambdaSquareForm_apply (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int)
    (τ : _root_.UpperHalfPlane) :
    lambdaSquareForm N hN a b τ = TorsionWeierstrassData.lambdaValue N a b τ ^ 2 := by
  rw [lambdaSquareForm, lambdaProductForm_apply]
  ring

/-- The actual all-label relation between λ², x and μ as an equality of modular forms. -/
theorem lambdaSquareForm_eq_x_add_mu (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int) :
    lambdaSquareForm N hN a b = WeierstrassForms.xForm N hN a b +
      (2 : ℂ) • WeierstrassForms.muForm N hN a b := by
  let _ : NeZero N := ⟨hN.ne'⟩
  apply DFunLike.ext
  intro τ
  change lambdaSquareForm N hN a b τ = WeierstrassForms.xForm N hN a b τ +
    (2 : ℂ) * WeierstrassForms.muForm N hN a b τ
  rw [lambdaSquareForm_apply, WeierstrassForms.xForm_apply, WeierstrassForms.muForm_apply]
  exact TorsionQuadraticCases.lambdaValue_square a b τ

/-- The actual square belongs to the series span without any good-label restriction. -/
theorem lambdaSquareForm_mem_divisionSpan (N : _root_.Nat) (hN : 0 < N) (a b : _root_.Int) :
    lambdaSquareForm N hN a b ∈ divisionSpan N hN := by
  rw [lambdaSquareForm_eq_x_add_mu]
  exact (divisionSpan N hN).add_mem (xForm_mem_divisionSpan N hN a b)
    ((divisionSpan N hN).smul_mem 2 (muForm_mem_divisionSpan N hN a b))

/-- The actual quadratic defect as a difference of products of genuine weight-one forms. -/
def quadraticDefectForm (N : _root_.Nat) (hN : 0 < N) (a b c d : _root_.Int) : WeightTwo N :=
  lambdaProductForm N hN a b c d -
    lambdaProductForm N hN a b (a + c) (b + d) -
    lambdaProductForm N hN c d (a + c) (b + d)

theorem quadraticDefectForm_apply (N : _root_.Nat) (hN : 0 < N) (a b c d : _root_.Int)
    (τ : _root_.UpperHalfPlane) :
    quadraticDefectForm N hN a b c d τ = TorsionQuadraticCases.quadraticDefect N a b c d τ := by
  change lambdaProductForm N hN a b c d τ - lambdaProductForm N hN a b (a + c) (b + d) τ -
    lambdaProductForm N hN c d (a + c) (b + d) τ = _
  simp only [lambdaProductForm_apply, TorsionQuadraticCases.quadraticDefect]

/-- A bad first label gives the negative square of the second label, not three μ terms. -/
theorem quadraticDefectForm_of_bad_left (N : _root_.Nat) (hN : 0 < N) (a b c d : _root_.Int)
    (hp : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) :
    quadraticDefectForm N hN a b c d = -lambdaSquareForm N hN c d := by
  let _ : NeZero N := ⟨hN.ne'⟩
  apply DFunLike.ext
  intro τ
  change quadraticDefectForm N hN a b c d τ = -lambdaSquareForm N hN c d τ
  rw [quadraticDefectForm_apply, lambdaSquareForm_apply, TorsionQuadraticCases.lambdaValue_square]
  exact TorsionQuadraticCases.defect_of_bad_left a b c d τ hp

/-- A bad second label gives the negative square of the first label. -/
theorem quadraticDefectForm_of_bad_right (N : _root_.Nat) (hN : 0 < N) (a b c d : _root_.Int)
    (hq : (N : ℤ) ∣ c ∧ (N : ℤ) ∣ d) :
    quadraticDefectForm N hN a b c d = -lambdaSquareForm N hN a b := by
  let _ : NeZero N := ⟨hN.ne'⟩
  apply DFunLike.ext
  intro τ
  change quadraticDefectForm N hN a b c d τ = -lambdaSquareForm N hN a b τ
  rw [quadraticDefectForm_apply, lambdaSquareForm_apply, TorsionQuadraticCases.lambdaValue_square]
  exact TorsionQuadraticCases.defect_of_bad_right a b c d τ hq

/-- A bad sum gives the negative square of the first label. -/
theorem quadraticDefectForm_of_bad_sum (N : _root_.Nat) (hN : 0 < N) (a b c d : _root_.Int)
    (hs : (N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d) :
    quadraticDefectForm N hN a b c d = -lambdaSquareForm N hN a b := by
  let _ : NeZero N := ⟨hN.ne'⟩
  apply DFunLike.ext
  intro τ
  change quadraticDefectForm N hN a b c d τ = -lambdaSquareForm N hN a b τ
  rw [quadraticDefectForm_apply, lambdaSquareForm_apply, TorsionQuadraticCases.lambdaValue_square]
  exact TorsionQuadraticCases.defect_of_bad_sum a b c d τ hs

/-- The three-μ formula is used only when all three torsion classes are good. -/
theorem quadraticDefectForm_of_three_good (N : _root_.Nat) (hN : 0 < N) (a b c d : _root_.Int)
    (hp : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b))
    (hq : ¬ ((N : ℤ) ∣ c ∧ (N : ℤ) ∣ d))
    (hs : ¬ ((N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d)) :
    quadraticDefectForm N hN a b c d = -WeierstrassForms.muForm N hN a b -
      WeierstrassForms.muForm N hN c d - WeierstrassForms.muForm N hN (a + c) (b + d) := by
  let _ : NeZero N := ⟨hN.ne'⟩
  apply DFunLike.ext
  intro τ
  change quadraticDefectForm N hN a b c d τ = -WeierstrassForms.muForm N hN a b τ -
    WeierstrassForms.muForm N hN c d τ - WeierstrassForms.muForm N hN (a + c) (b + d) τ
  rw [quadraticDefectForm_apply, WeierstrassForms.muForm_apply,
    WeierstrassForms.muForm_apply, WeierstrassForms.muForm_apply]
  simpa only [ite_eq_right hp, ite_eq_right hq, ite_eq_right hs] using
    TorsionQuadraticCases.quadraticDefect_cases (N := N) a b c d τ

/-- Complete-case membership of every actual quadratic defect in the independent series span. -/
theorem quadraticDefectForm_mem_divisionSpan (N : _root_.Nat) (hN : 0 < N) (a b c d : _root_.Int) :
    quadraticDefectForm N hN a b c d ∈ divisionSpan N hN := by
  classical
  by_cases hp : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · rw [quadraticDefectForm_of_bad_left N hN a b c d hp]
    exact (divisionSpan N hN).neg_mem (lambdaSquareForm_mem_divisionSpan N hN c d)
  · by_cases hq : (N : ℤ) ∣ c ∧ (N : ℤ) ∣ d
    · rw [quadraticDefectForm_of_bad_right N hN a b c d hq]
      exact (divisionSpan N hN).neg_mem (lambdaSquareForm_mem_divisionSpan N hN a b)
    · by_cases hs : (N : ℤ) ∣ a + c ∧ (N : ℤ) ∣ b + d
      · rw [quadraticDefectForm_of_bad_sum N hN a b c d hs]
        exact (divisionSpan N hN).neg_mem (lambdaSquareForm_mem_divisionSpan N hN a b)
      · rw [quadraticDefectForm_of_three_good N hN a b c d hp hq hs]
        exact (divisionSpan N hN).sub_mem
          ((divisionSpan N hN).sub_mem
            ((divisionSpan N hN).neg_mem (muForm_mem_divisionSpan N hN a b))
            (muForm_mem_divisionSpan N hN c d))
          (muForm_mem_divisionSpan N hN (a + c) (b + d))

/-- At level one all labels are bad, so the actual defect form is zero. -/
theorem quadraticDefectForm_level_one (h1 : 0 < (1 : ℕ)) (a b c d : _root_.Int) :
    quadraticDefectForm 1 h1 a b c d = 0 := by
  rw [quadraticDefectForm_of_bad_left 1 h1 a b c d (by simp)]
  apply DFunLike.ext
  intro τ
  change -lambdaSquareForm 1 h1 c d τ = (0 : ℂ)
  rw [lambdaSquareForm_apply]
  have h := TorsionQuadraticCases.lambdaValue_of_bad (N := 1) c d τ (by simp)
  rw [h]
  ring

end ZInQ.Contrib.HeckePrimeRationality.DivisionSeriesMembership
