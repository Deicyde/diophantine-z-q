import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimeProductTraceDeterminantFourier
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelation
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionQuadraticGeneratorSpan
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinTracePartial

/-!
# Actual zero-extended weight-one torsion products

Every product is an actual weight-two principal modular form. On admissible
labels it is the constant κ² times the genuine degree-two principal product;
zero labels contribute zero, not the unregularized bad torsion value.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace

open TorsionCorrelation TorsionQuadraticGenerators AllLevelProducts DivisionEisensteinLevelMaps

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- The actual completed weight-one form on a residue point. -/
def lambdaPointForm (N : ℕ) (hN : 0 < N) (P : Point N) : _root_.ModularForm (ΓP N) 1 :=
  lambdaForm N hN (P.1.val : ℤ) (P.2.val : ℤ)

/-- An actual weight-two product at the given principal level. -/
def lambdaProduct (N : ℕ) (hN : 0 < N) (P Q : Point N) : _root_.ModularForm (ΓP N) 2 :=
  (lambdaPointForm N hN P).mul (lambdaPointForm N hN Q)

theorem lambdaPointForm_apply (N : ℕ) (hN : 0 < N) (P : Point N) (τ : ℍ) :
    lambdaPointForm N hN P τ = TorsionWeierstrassData.scale * TorsionCorrelation.h N τ P := by
  rw [lambdaPointForm, lambdaForm_apply]
  rfl

theorem lambdaProduct_apply (N : ℕ) (hN : 0 < N) (P Q : Point N) (τ : ℍ) :
    lambdaProduct N hN P Q τ = TorsionWeierstrassData.scale ^ 2 *
      (TorsionCorrelation.h N τ P * TorsionCorrelation.h N τ Q) := by
  change lambdaPointForm N hN P τ * lambdaPointForm N hN Q τ = _
  rw [lambdaPointForm_apply, lambdaPointForm_apply]
  ring

theorem lambdaProduct_label_apply (N : ℕ) (hN : 0 < N) (a b c d : ℤ) (τ : ℍ) :
    lambdaProduct N hN (label N a b) (label N c d) τ =
      TorsionWeierstrassData.lambdaValue N a b τ * TorsionWeierstrassData.lambdaValue N c d τ := by
  rw [lambdaProduct_apply, h_label hN, h_label hN]
  unfold TorsionWeierstrassData.lambdaValue
  ring

/-- Good integer labels give exactly the genuine productForm, with only the
fixed complex scale relating h to λ. -/
theorem lambdaProduct_eq_principal_product (N : ℕ) (hN : 0 < N) (a b c d : ℤ)
    (hP : AllLevelForms.Good N (a,b)) (hQ : AllLevelForms.Good N (c,d)) :
    lambdaProduct N hN (label N a b) (label N c d) = TorsionWeierstrassData.scale ^ 2 •
      productForm N hN 2 ![(a,b),(c,d)] (by intro i; fin_cases i <;> assumption) := by
  apply _root_.ModularForm.ext
  intro τ
  rw [lambdaProduct_label_apply, TorsionWeierstrassData.lambdaValue_of_good N a b τ hP,
    TorsionWeierstrassData.lambdaValue_of_good N c d τ hQ, smul_apply, smul_eq_mul]
  have hp := productForm_apply hN 2 ![(a,b),(c,d)]
    (show ∀ i : Fin 2, AllLevelForms.Good N (![(a,b),(c,d)] i) from by
      intro i; fin_cases i <;> assumption) τ
  rw [hp, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Prod.fst, Prod.snd]
  ring

/-- The rank-zero trace case is already a product at the lower level. -/
theorem rank_zero_principal_product_trace (t N : ℕ) (ht : 0 < t) (hN : 0 < N) (a b c d : ℤ)
    (hP : AllLevelForms.Good N (a,b)) (hQ : AllLevelForms.Good N (c,d)) :
    let hPt : AllLevelForms.Good (t * N) ((t : ℤ) * a,(t : ℤ) * b) := by
      intro hb
      apply hP
      have htZ : (t : ℤ) ≠ 0 := by exact_mod_cast ht.ne'
      simpa only [Nat.cast_mul, mul_dvd_mul_iff_left htZ] using hb
    let hQt : AllLevelForms.Good (t * N) ((t : ℤ) * c,(t : ℤ) * d) := by
      intro hb
      apply hQ
      have htZ : (t : ℤ) ≠ 0 := by exact_mod_cast ht.ne'
      simpa only [Nat.cast_mul, mul_dvd_mul_iff_left htZ] using hb
    normalizedTrace N (t * N) (Nat.mul_pos ht hN)
      (productForm (t * N) (Nat.mul_pos ht hN) 2
        ![((t : ℤ) * a,(t : ℤ) * b),((t : ℤ) * c,(t : ℤ) * d)]
        (by intro i; fin_cases i <;> assumption)) ∈ productSpan N hN := by
  dsimp only
  have hPt : AllLevelForms.Good (t * N) ((t : ℤ) * a,(t : ℤ) * b) := by
    intro hb
    apply hP
    have htZ : (t : ℤ) ≠ 0 := by exact_mod_cast ht.ne'
    simpa only [Nat.cast_mul, mul_dvd_mul_iff_left htZ] using hb
  have hQt : AllLevelForms.Good (t * N) ((t : ℤ) * c,(t : ℤ) * d) := by
    intro hb
    apply hQ
    have htZ : (t : ℤ) ≠ 0 := by exact_mod_cast ht.ne'
    simpa only [Nat.cast_mul, mul_dvd_mul_iff_left htZ] using hb
  let F := productForm N hN 2 ![(a,b),(c,d)]
    (show ∀ i : Fin 2, AllLevelForms.Good N (![(a,b),(c,d)] i) from by
      intro i; fin_cases i <;> assumption)
  have he : productForm (t * N) (Nat.mul_pos ht hN) 2
      ![((t : ℤ) * a,(t : ℤ) * b),((t : ℤ) * c,(t : ℤ) * d)]
      (show ∀ i : Fin 2, AllLevelForms.Good (t * N)
        (![((t : ℤ) * a,(t : ℤ) * b),((t : ℤ) * c,(t : ℤ) * d)] i) from by
          intro i; fin_cases i <;> assumption) = restriction N (t * N) (dvd_mul_left N t) F := by
    apply _root_.ModularForm.ext
    intro τ
    rw [restriction_apply, productForm_apply, Fin.prod_univ_two]
    change Torsion.torsionLogDerivative (t * N) ((t : ℤ) * a) ((t : ℤ) * b) τ *
        Torsion.torsionLogDerivative (t * N) ((t : ℤ) * c) ((t : ℤ) * d) τ = F τ
    rw [TorsionCorrelation.raw_scale t N ht hN, TorsionCorrelation.raw_scale t N ht hN]
    dsimp only [F]
    rw [productForm_apply, Fin.prod_univ_two]
    rfl
  rw [he, normalizedTrace_restriction (Nat.mul_pos ht hN) (dvd_mul_left N t) F]
  apply Submodule.subset_span
  exact ⟨![(a,b),(c,d)], (by intro i; fin_cases i <;> assumption), rfl⟩

end ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace
