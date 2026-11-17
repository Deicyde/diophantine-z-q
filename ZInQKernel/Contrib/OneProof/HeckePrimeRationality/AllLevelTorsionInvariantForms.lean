import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionInvariants

/-!
# Actual Weierstrass invariant forms in same-level torsion product spans

Finite torsion polynomials construct weight-four and weight-six modular
forms whose values are the actual lattice invariants. Products of genuine
admissible torsion tuples are concatenated, with no whole-space generation
assumption. The lattice Eisenstein sums of weights four and six retain
their actual Mathlib definitions and normalizations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open Complex ModularForm
open scoped Topology Real UpperHalfPlane Modular MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionInvariantForms

open ZInQ.Contrib.HeckePrimeRationality
open TorsionInvariants TorsionWeierstrassData TorsionWeightThree

/-- The span of actual admissible length-k torsion products, at the same level N. -/
def homogeneousProductSpan (N : ℕ) (hN : 0 < N) (k : ℕ) : Submodule ℂ (Weight N (k : ℤ)) :=
  Submodule.span ℂ {f | ∃ v : Fin k → ℤ × ℤ, ∃ hv : ∀ i, AllLevelForms.Good N (v i),
    f = AllLevelProducts.productForm N hN k v hv}

/-- Actual modular-form multiplication with its homogeneous weight placed in the natural-number grade. -/
def productMul (N : ℕ) (k l : ℕ) (f : Weight N (k : ℤ)) (g : Weight N (l : ℤ)) :
    Weight N ((k + l : ℕ) : ℤ) := ModularForm.mcast (by push_cast; ring) (f.mul g)

lemma productMul_apply (N k l : ℕ) (f : Weight N (k : ℤ)) (g : Weight N (l : ℤ)) (τ : ℍ) :
    productMul N k l f g τ = f τ * g τ := rfl

lemma productMul_add_left (N k l : ℕ) (f f' : Weight N (k : ℤ)) (g : Weight N (l : ℤ)) :
    productMul N k l (f + f') g = productMul N k l f g + productMul N k l f' g := by
  apply DFunLike.ext
  intro τ
  change (f τ + f' τ) * g τ = f τ * g τ + f' τ * g τ
  ring

lemma productMul_add_right (N k l : ℕ) (f : Weight N (k : ℤ)) (g g' : Weight N (l : ℤ)) :
    productMul N k l f (g + g') = productMul N k l f g + productMul N k l f g' := by
  apply DFunLike.ext
  intro τ
  change f τ * (g τ + g' τ) = f τ * g τ + f τ * g' τ
  ring

lemma productMul_smul_left (N k l : ℕ) (c : ℂ) (f : Weight N (k : ℤ)) (g : Weight N (l : ℤ)) :
    productMul N k l (c • f) g = c • productMul N k l f g := by
  apply DFunLike.ext
  intro τ
  change (c * f τ) * g τ = c * (f τ * g τ)
  ring

lemma productMul_smul_right (N k l : ℕ) (c : ℂ) (f : Weight N (k : ℤ)) (g : Weight N (l : ℤ)) :
    productMul N k l f (c • g) = c • productMul N k l f g := by
  apply DFunLike.ext
  intro τ
  change f τ * (c * g τ) = c * (f τ * g τ)
  ring

lemma productMul_zero_left (N k l : ℕ) (g : Weight N (l : ℤ)) : productMul N k l 0 g = 0 := by
  apply DFunLike.ext
  intro τ
  change (0 : ℂ) * g τ = 0
  ring

lemma productMul_zero_right (N k l : ℕ) (f : Weight N (k : ℤ)) : productMul N k l f 0 = 0 := by
  apply DFunLike.ext
  intro τ
  change f τ * (0 : ℂ) = 0
  ring

/-- Concatenation is actual multiplication of the two genuine product tuples. -/
lemma productMul_generators (N : ℕ) (hN : 0 < N) (k l : ℕ)
    (v : Fin k → ℤ × ℤ) (w : Fin l → ℤ × ℤ)
    (hv : ∀ i, AllLevelForms.Good N (v i)) (hw : ∀ i, AllLevelForms.Good N (w i)) :
    ∃ h : ∀ i : Fin (k + l), AllLevelForms.Good N (Fin.append v w i),
      productMul N k l (AllLevelProducts.productForm N hN k v hv)
        (AllLevelProducts.productForm N hN l w hw) =
      AllLevelProducts.productForm N hN (k + l) (Fin.append v w) h := by
  have h : ∀ i : Fin (k + l), AllLevelForms.Good N (Fin.append v w i) := by
    intro i
    exact Fin.addCases (fun j => by simpa only [Fin.append_left] using hv j)
      (fun j => by simpa only [Fin.append_right] using hw j) i
  refine ⟨h, ?_⟩
  apply DFunLike.ext
  intro τ
  rw [productMul_apply, AllLevelProducts.productForm_apply hN k v hv,
    AllLevelProducts.productForm_apply hN l w hw,
    AllLevelProducts.productForm_apply hN (k + l) (Fin.append v w) h, Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right]

/-- Multiplication of two independent product spans stays in the concatenated product span. -/
theorem productMul_mem (N : ℕ) (hN : 0 < N) (k l : ℕ)
    (f : Weight N (k : ℤ)) (g : Weight N (l : ℤ))
    (hf : f ∈ homogeneousProductSpan N hN k) (hg : g ∈ homogeneousProductSpan N hN l) :
    productMul N k l f g ∈ homogeneousProductSpan N hN (k + l) := by
  classical
  induction hf using Submodule.span_induction with
  | mem f hf =>
    rcases hf with ⟨v, hv, rfl⟩
    induction hg using Submodule.span_induction with
    | mem g hg =>
      rcases hg with ⟨w, hw, rfl⟩
      obtain ⟨h, he⟩ := productMul_generators N hN k l v w hv hw
      rw [he]
      apply Submodule.subset_span
      exact ⟨Fin.append v w, h, rfl⟩
    | zero =>
      rw [productMul_zero_right]
      exact (homogeneousProductSpan N hN (k + l)).zero_mem
    | add g g' hg hg' ih ih' =>
      rw [productMul_add_right]
      exact (homogeneousProductSpan N hN (k + l)).add_mem ih ih'
    | smul c g hg ih =>
      rw [productMul_smul_right]
      exact (homogeneousProductSpan N hN (k + l)).smul_mem c ih
  | zero =>
    rw [productMul_zero_left]
    exact (homogeneousProductSpan N hN (k + l)).zero_mem
  | add f f' hf hf' ih ih' =>
    rw [productMul_add_left]
    exact (homogeneousProductSpan N hN (k + l)).add_mem ih ih'
  | smul c f hf ih =>
    rw [productMul_smul_left]
    exact (homogeneousProductSpan N hN (k + l)).smul_mem c ih

lemma xForm_mem_homogeneous (N : ℕ) (hN : 0 < N) (h3 : 3 ≤ N) (a b : ℤ) :
    WeierstrassForms.xForm N hN a b ∈ homogeneousProductSpan N hN 2 := by
  rw [TorsionWeightThree.xForm_eq_quadratic_generator N hN h3 a b]
  exact TorsionQuadraticGenerators.xForm_mem_productSpan N h3 a b

lemma yForm_mem_homogeneous (N : ℕ) (hN : 0 < N) (h3 : 3 ≤ N) (a b : ℤ) :
    TorsionWeightThree.yForm N hN a b ∈ homogeneousProductSpan N hN 3 :=
  TorsionWeightThree.yForm_mem_degreeThree N hN h3 a b

/-- The actual square of the actual x-form. -/
def xSquareForm (N : ℕ) (hN : 0 < N) (a b : ℤ) : Weight N 4 :=
  productMul N 2 2 (WeierstrassForms.xForm N hN a b) (WeierstrassForms.xForm N hN a b)

lemma xSquareForm_apply (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    xSquareForm N hN a b τ = xValue N a b τ ^ 2 := by
  rw [xSquareForm, productMul_apply, WeierstrassForms.xForm_apply]
  ring

/-- The actual cube of the actual x-form. -/
def xCubeForm (N : ℕ) (hN : 0 < N) (a b : ℤ) : Weight N 6 :=
  productMul N 2 4 (WeierstrassForms.xForm N hN a b) (xSquareForm N hN a b)

lemma xCubeForm_apply (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    xCubeForm N hN a b τ = xValue N a b τ ^ 3 := by
  rw [xCubeForm, productMul_apply, WeierstrassForms.xForm_apply, xSquareForm_apply]
  ring

/-- The actual square of the actual full Weierstrass derivative form. -/
def ySquareForm (N : ℕ) (hN : 0 < N) (a b : ℤ) : Weight N 6 :=
  productMul N 3 3 (TorsionWeightThree.yForm N hN a b) (TorsionWeightThree.yForm N hN a b)

lemma ySquareForm_apply (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    ySquareForm N hN a b τ = yValue N a b τ ^ 2 := by
  rw [ySquareForm, productMul_apply, TorsionWeightThree.yForm_apply]
  ring

/-- The finite torsion-polynomial form of weight four. Its value is proved to be the actual g₂ invariant. -/
def g2Form (N : ℕ) (h2 : 2 ≤ N) : Weight N 4 :=
  (((N : ℂ) ^ 2 - 1) * ((N : ℂ) ^ 2 + 6))⁻¹ • (60 : ℂ) •
    ∑ p ∈ nonzeroIndices N (by omega), xSquareForm N (by omega) (p.1 : ℕ) (p.2 : ℕ)

/-- The finite torsion-polynomial form of weight six. Its value is proved to be the actual g₃ invariant. -/
def g3Form (N : ℕ) (h2 : 2 ≤ N) : Weight N 6 :=
  ((N : ℂ) ^ 2 - 1)⁻¹ •
    ((4 : ℂ) • ∑ p ∈ nonzeroIndices N (by omega), xCubeForm N (by omega) (p.1 : ℕ) (p.2 : ℕ) -
      ∑ p ∈ nonzeroIndices N (by omega), ySquareForm N (by omega) (p.1 : ℕ) (p.2 : ℕ))

/-- Literal value equality with Mathlib's actual lattice-defined g₂, with no desired normalization premise. -/
theorem g2Form_apply_actual (N : ℕ) (h2 : 2 ≤ N) (τ : ℍ) :
    g2Form N h2 τ = (ThetaWeierstrass.periodPair τ).g₂ := by
  simp only [g2Form, _root_.smul_apply, _root_.sum_apply, smul_eq_mul, xSquareForm_apply]
  rw [g2_eq_torsion_polynomial N h2 τ]
  ring

/-- Literal value equality with Mathlib's actual lattice-defined g₃ using full WP′, not WP′/2. -/
theorem g3Form_apply_actual (N : ℕ) (h2 : 2 ≤ N) (τ : ℍ) :
    g3Form N h2 τ = (ThetaWeierstrass.periodPair τ).g₃ := by
  simp only [g3Form, _root_.smul_apply, _root_.sum_apply, _root_.sub_apply, smul_eq_mul,
    xCubeForm_apply, ySquareForm_apply]
  rw [g3_eq_torsion_polynomial N h2 τ]
  ring

lemma xSquareForm_mem (N : ℕ) (hN : 0 < N) (h3 : 3 ≤ N) (a b : ℤ) :
    xSquareForm N hN a b ∈ homogeneousProductSpan N hN 4 :=
  productMul_mem N hN 2 2 _ _ (xForm_mem_homogeneous N hN h3 a b) (xForm_mem_homogeneous N hN h3 a b)

lemma xCubeForm_mem (N : ℕ) (hN : 0 < N) (h3 : 3 ≤ N) (a b : ℤ) :
    xCubeForm N hN a b ∈ homogeneousProductSpan N hN 6 :=
  productMul_mem N hN 2 4 _ _ (xForm_mem_homogeneous N hN h3 a b) (xSquareForm_mem N hN h3 a b)

lemma ySquareForm_mem (N : ℕ) (hN : 0 < N) (h3 : 3 ≤ N) (a b : ℤ) :
    ySquareForm N hN a b ∈ homogeneousProductSpan N hN 6 :=
  productMul_mem N hN 3 3 _ _ (yForm_mem_homogeneous N hN h3 a b) (yForm_mem_homogeneous N hN h3 a b)

/-- The actual g₂ invariant form belongs to the SAME-level actual degree-four product span for N≥3. -/
theorem g2Form_mem_degreeFour (N : ℕ) (h3 : 3 ≤ N) :
    g2Form N (by omega) ∈ homogeneousProductSpan N (by omega) 4 := by
  unfold g2Form
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro p _
  exact xSquareForm_mem N (by omega) h3 (p.1 : ℕ) (p.2 : ℕ)

/-- The actual g₃ invariant form belongs to the SAME-level actual degree-six product span for N≥3. -/
theorem g3Form_mem_degreeSix (N : ℕ) (h3 : 3 ≤ N) :
    g3Form N (by omega) ∈ homogeneousProductSpan N (by omega) 6 := by
  unfold g3Form
  apply Submodule.smul_mem
  apply Submodule.sub_mem
  · apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro p _
    exact xCubeForm_mem N (by omega) h3 (p.1 : ℕ) (p.2 : ℕ)
  · apply Submodule.sum_mem
    intro p _
    exact ySquareForm_mem N (by omega) h3 (p.1 : ℕ) (p.2 : ℕ)

/-- The actual weight-four lattice Eisenstein form retains the normalization g₂ = 60 G₄. -/
def latticeG4Form (N : ℕ) (h2 : 2 ≤ N) : Weight N 4 := (1 / 60 : ℂ) • g2Form N h2

/-- The actual weight-six lattice Eisenstein form retains the normalization g₃ = 140 G₆. -/
def latticeG6Form (N : ℕ) (h2 : 2 ≤ N) : Weight N 6 := (1 / 140 : ℂ) • g3Form N h2

theorem latticeG4Form_apply (N : ℕ) (h2 : 2 ≤ N) (τ : ℍ) :
    latticeG4Form N h2 τ = (ThetaWeierstrass.periodPair τ).G 4 := by
  change (1 / 60 : ℂ) * g2Form N h2 τ = _
  rw [g2Form_apply_actual, PeriodPair.g₂]
  ring

theorem latticeG6Form_apply (N : ℕ) (h2 : 2 ≤ N) (τ : ℍ) :
    latticeG6Form N h2 τ = (ThetaWeierstrass.periodPair τ).G 6 := by
  change (1 / 140 : ℂ) * g3Form N h2 τ = _
  rw [g3Form_apply_actual, PeriodPair.g₃]
  ring

theorem latticeG4Form_mem_degreeFour (N : ℕ) (h3 : 3 ≤ N) :
    latticeG4Form N (by omega) ∈ homogeneousProductSpan N (by omega) 4 :=
  (homogeneousProductSpan N (by omega) 4).smul_mem _ (g2Form_mem_degreeFour N h3)

theorem latticeG6Form_mem_degreeSix (N : ℕ) (h3 : 3 ≤ N) :
    latticeG6Form N (by omega) ∈ homogeneousProductSpan N (by omega) 6 :=
  (homogeneousProductSpan N (by omega) 6).smul_mem _ (g3Form_mem_degreeSix N h3)

end ZInQ.Contrib.HeckePrimeRationality.TorsionInvariantForms
