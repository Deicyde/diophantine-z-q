import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionWeightThreeFourier
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionWeierstrassForms
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionQuadraticGeneratorSpan

/-!
# Actual weight-three torsion forms and same-level product generators

Finite cubic Fourier inversion constructs a genuine modular form whose
values are the actual Weierstrass derivative. At levels at least three,
the verified quadratic x-generators show that this form belongs to the
span of actual admissible degree-three principal torsion products.
No whole-space spanning or Hecke conclusion is asserted.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open Complex ModularForm
open scoped Real UpperHalfPlane Modular MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionWeightThree

open ZInQ.Contrib.HeckePrimeRationality
open TorsionWeierstrassData

/-- The actual principal-congruence modular-form ambient space. -/
abbrev Weight (N : ℕ) (k : ℤ) := ModularForm ((CongruenceSubgroup.Gamma N).map
  (Matrix.SpecialLinearGroup.mapGL ℝ)) k

/-- Multiplication by the actual completed weight-one torsion form. -/
def lambdaTimesForm (N : ℕ) (hN : 0 < N) (a b : ℤ) (g : Weight N 2) : Weight N 3 :=
  ModularForm.mcast (by norm_num) ((WeierstrassForms.lambdaForm N hN a b).mul g)

lemma lambdaTimesForm_apply (N : ℕ) (hN : 0 < N) (a b : ℤ) (g : Weight N 2) (τ : ℍ) :
    lambdaTimesForm N hN a b g τ = lambdaValue N a b τ * g τ := by
  change WeierstrassForms.lambdaForm N hN a b τ * g τ = _
  rw [WeierstrassForms.lambdaForm_apply]

/-- The actual cube of the completed weight-one torsion form. -/
def lambdaCubeForm (N : ℕ) (hN : 0 < N) (a b : ℤ) : Weight N 3 :=
  lambdaTimesForm N hN a b
    (TorsionQuadraticGenerators.lambdaSquare N hN a b)

lemma lambdaCubeForm_apply (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    lambdaCubeForm N hN a b τ = lambdaValue N a b τ ^ 3 := by
  rw [lambdaCubeForm, lambdaTimesForm_apply, TorsionQuadraticGenerators.lambdaSquare_apply]
  ring

/-- The genuine weight-three form with actual values λ³−3λx. -/
def cubicForm (N : ℕ) (hN : 0 < N) (a b : ℤ) : Weight N 3 :=
  lambdaCubeForm N hN a b - (3 : ℂ) •
    lambdaTimesForm N hN a b (WeierstrassForms.xForm N hN a b)

lemma cubicForm_apply (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    cubicForm N hN a b τ = cubicValue N a b τ := by
  change lambdaCubeForm N hN a b τ - (3 : ℂ) *
    lambdaTimesForm N hN a b (WeierstrassForms.xForm N hN a b) τ = _
  rw [lambdaCubeForm_apply, lambdaTimesForm_apply, WeierstrassForms.xForm_apply, cubicValue]
  ring

/-- The actual Weierstrass derivative as a modular form built by proved finite cubic inversion. -/
def yForm (N : ℕ) (hN : 0 < N) (r s : ℤ) : Weight N 3 :=
  ((N : ℂ) ^ 4 - 9)⁻¹ •
    ((3 * (N : ℂ)) • ∑ p : Fin N × Fin N,
      TorsionFourierComparison.character N (p.1 : ℕ) (p.2 : ℕ) r s •
        cubicForm N hN (p.1 : ℕ) (p.2 : ℕ) - (N : ℂ) ^ 4 • cubicForm N hN r s)

/-- The finite cubic construction evaluates to the actual WP′ function on every integer label. -/
theorem yForm_apply (N : ℕ) (hN : 0 < N) (r s : ℤ) (τ : ℍ) :
    yForm N hN r s τ = yValue N r s τ := by
  let _ : NeZero N := ⟨hN.ne'⟩
  simp only [yForm, _root_.smul_apply, _root_.sum_apply, _root_.sub_apply, smul_eq_mul,
    cubicForm_apply]
  rw [yValue_cubic_formula N τ r s]
  simp only [mul_comm (TorsionFourierComparison.character N _ _ _ _) _, div_eq_mul_inv]
  ring

/-- Literal actual-object evaluation, including the proved bad-class zero values. -/
theorem yForm_apply_actual (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    yForm N hN a b τ =
      (ThetaWeierstrass.periodPair τ).derivWeierstrassP (CompletedTheta.torsionPoint N a b τ) := by
  rw [yForm_apply, yValue_eq_actual N hN]

theorem yForm_of_bad (N : ℕ) (hN : 0 < N) (a b : ℤ)
    (hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) : yForm N hN a b = 0 := by
  apply DFunLike.ext
  intro τ
  rw [yForm_apply, yValue_of_bad N a b τ hb]
  rfl

theorem yForm_neg (N : ℕ) (hN : 0 < N) (a b : ℤ) : yForm N hN (-a) (-b) = -yForm N hN a b := by
  apply DFunLike.ext
  intro τ
  change yForm N hN (-a) (-b) τ = -yForm N hN a b τ
  rw [yForm_apply, yForm_apply, yValue_neg N hN]

theorem yForm_shift (N : ℕ) (hN : 0 < N) (a b m n : ℤ) :
    yForm N hN (a + N * m) (b + N * n) = yForm N hN a b := by
  apply DFunLike.ext
  intro τ
  rw [yForm_apply, yForm_apply, yValue_shift N hN]

theorem yForm_level_one (h1 : 0 < (1 : ℕ)) (a b : ℤ) : yForm 1 h1 a b = 0 :=
  yForm_of_bad 1 h1 a b (by simp)

/-- The span of actual admissible degree-three torsion products, at the same positive level. -/
def degreeThreeProductSpan (N : ℕ) (hN : 0 < N) : Submodule ℂ (Weight N 3) :=
  Submodule.span ℂ {f | ∃ v : Fin 3 → ℤ × ℤ, ∃ hv : ∀ i, AllLevelForms.Good N (v i),
    f = AllLevelProducts.productForm N hN 3 v hv}

/-- Multiplication by one actual weight-one factor carries the degree-two generator span
into the degree-three generator span. Bad labels contribute the proved zero form. -/
theorem lambdaTimesForm_mem_degreeThree (N : ℕ) (hN : 0 < N) (a b : ℤ)
    (g : Weight N 2) (hg : g ∈ TorsionQuadraticGenerators.productSpan N hN) :
    lambdaTimesForm N hN a b g ∈ degreeThreeProductSpan N hN := by
  classical
  by_cases ha : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · have he : lambdaTimesForm N hN a b g = 0 := by
      apply DFunLike.ext
      intro τ
      rw [lambdaTimesForm_apply]
      simp [lambdaValue, TorsionDistributionTwo.reg_of_bad ha]
    rw [he]
    exact (degreeThreeProductSpan N hN).zero_mem
  · induction hg using Submodule.span_induction with
    | mem f hf =>
      rcases hf with ⟨v, hv, rfl⟩
      let w : Fin 3 → ℤ × ℤ := Fin.cons (a, b) v
      have hw : ∀ i : Fin 3, AllLevelForms.Good N (w i) := Fin.cases ha hv
      have he : lambdaTimesForm N hN a b (AllLevelProducts.productForm N hN 2 v hv) =
          scale • AllLevelProducts.productForm N hN 3 w hw := by
        apply DFunLike.ext
        intro τ
        change lambdaTimesForm N hN a b (AllLevelProducts.productForm N hN 2 v hv) τ =
          scale * AllLevelProducts.productForm N hN 3 w hw τ
        rw [lambdaTimesForm_apply, lambdaValue_of_good N a b τ ha,
          AllLevelProducts.productForm_apply hN 2 v hv, AllLevelProducts.productForm_apply hN 3 w hw]
        simp only [w, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
        ring
      rw [he]
      apply (degreeThreeProductSpan N hN).smul_mem
      apply Submodule.subset_span
      exact ⟨w, hw, rfl⟩
    | zero =>
      have he : lambdaTimesForm N hN a b 0 = 0 := by
        apply DFunLike.ext
        intro τ
        simp [lambdaTimesForm_apply]
      rw [he]
      exact (degreeThreeProductSpan N hN).zero_mem
    | add f g hf hg ihf ihg =>
      have he : lambdaTimesForm N hN a b (f + g) =
          lambdaTimesForm N hN a b f + lambdaTimesForm N hN a b g := by
        apply DFunLike.ext
        intro τ
        simp [lambdaTimesForm_apply, mul_add]
      rw [he]
      exact (degreeThreeProductSpan N hN).add_mem ihf ihg
    | smul c f hf ih =>
      have he : lambdaTimesForm N hN a b (c • f) = c • lambdaTimesForm N hN a b f := by
        apply DFunLike.ext
        intro τ
        simp [lambdaTimesForm_apply, smul_eq_mul]
        ring
      rw [he]
      exact (degreeThreeProductSpan N hN).smul_mem c ih

/-- Every actual cube is already in the genuine degree-three product span. -/
theorem lambdaCubeForm_mem_degreeThree (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    lambdaCubeForm N hN a b ∈ degreeThreeProductSpan N hN :=
  lambdaTimesForm_mem_degreeThree N hN a b _
    (TorsionQuadraticGenerators.lambdaSquare_mem_productSpan N hN a b)

/-- The two independent actual x-bundles agree, so the verified quadratic generator inclusion applies. -/
theorem xForm_eq_quadratic_generator (N : ℕ) (hN : 0 < N) (h3 : 3 ≤ N) (a b : ℤ) :
    WeierstrassForms.xForm N hN a b = TorsionQuadraticGenerators.xForm N h3 a b := by
  let _ : NeZero N := ⟨hN.ne'⟩
  apply DFunLike.ext
  intro τ
  rw [WeierstrassForms.xForm_apply, TorsionQuadraticGenerators.xForm_apply]

/-- The actual cubic expression uses only genuine same-level degree-three product generators. -/
theorem cubicForm_mem_degreeThree (N : ℕ) (hN : 0 < N) (h3 : 3 ≤ N) (a b : ℤ) :
    cubicForm N hN a b ∈ degreeThreeProductSpan N hN := by
  have hx : WeierstrassForms.xForm N hN a b ∈ TorsionQuadraticGenerators.productSpan N hN := by
    rw [xForm_eq_quadratic_generator N hN h3 a b]
    exact TorsionQuadraticGenerators.xForm_mem_productSpan N h3 a b
  exact (degreeThreeProductSpan N hN).sub_mem (lambdaCubeForm_mem_degreeThree N hN a b)
    ((degreeThreeProductSpan N hN).smul_mem 3 (lambdaTimesForm_mem_degreeThree N hN a b _ hx))

/-- The actual WP′ modular form belongs to the genuine degree-three product span when N≥3. -/
theorem yForm_mem_degreeThree (N : ℕ) (hN : 0 < N) (h3 : 3 ≤ N) (a b : ℤ) :
    yForm N hN a b ∈ degreeThreeProductSpan N hN := by
  unfold yForm
  apply (degreeThreeProductSpan N hN).smul_mem
  apply (degreeThreeProductSpan N hN).sub_mem
  · apply (degreeThreeProductSpan N hN).smul_mem
    apply (degreeThreeProductSpan N hN).sum_mem
    intro p _
    exact (degreeThreeProductSpan N hN).smul_mem _ (cubicForm_mem_degreeThree N hN h3 (p.1 : ℕ) (p.2 : ℕ))
  · exact (degreeThreeProductSpan N hN).smul_mem _ (cubicForm_mem_degreeThree N hN h3 a b)

/-- An actual-object bundle and its same-level generator inclusion, without a wanted premise. -/
theorem actual_y_bundle_in_degreeThree (N : ℕ) (h3 : 3 ≤ N) (a b : ℤ) :
    ∃ f : Weight N 3, f ∈ degreeThreeProductSpan N (by omega) ∧
      ∀ τ : ℍ, f τ = (ThetaWeierstrass.periodPair τ).derivWeierstrassP
        (CompletedTheta.torsionPoint N a b τ) := by
  have hN : 0 < N := by omega
  exact ⟨yForm N hN a b, yForm_mem_degreeThree N hN h3 a b, yForm_apply_actual N hN a b⟩

end ZInQ.Contrib.HeckePrimeRationality.TorsionWeightThree
