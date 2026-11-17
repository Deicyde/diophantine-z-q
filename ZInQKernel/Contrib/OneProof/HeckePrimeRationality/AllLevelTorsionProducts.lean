import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionProductBase
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelIntegerRows

/-!
# Coefficient field and Galois covariance of homogeneous torsion products

For a positive level `N` and admissible labels `v₀, …, v_{k-1}`, the product form
`productForm N hN k v hv` on `Γ(N)` (whose values are `∏ᵢ F_{vᵢ}`) has the following
properties at the period `N`:

* (i) every coefficient of its `q`-expansion lies in the cyclotomic coefficient field
  `coefficientField N = ℚ(ζ_N)` (`productForm_coeff_mem`);
* (ii) for a field automorphism `σ` of `coefficientField N` with `σ ζ = ζ^t`, applying `σ` to every
  coefficient gives the coefficients of the product form with labels `(a, t b)`
  (`productForm_coeff_galois`);
* (iii) the `SL(2, ℤ)`-covariance of the product (`productForm_slash`, in the base file).

The expansion of the product is the product of the expansions of the factors (multiplicativity of
`q`-expansions of modular forms at a strict period), and the factorwise statements are the
integer-row coefficient theorems. The Galois action is applied to elements of the coefficient
field, never to complex values.
-/

noncomputable section

open ModularGroup UpperHalfPlane
open scoped Real MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelProducts

open CongruenceSubgroup Matrix.SpecialLinearGroup
open _root_.ZInQ.Contrib.HeckePrimeRationality.Torsion AllLevelForms AllLevelPrincipal
open AllLevelTorsionCoefficients (zetaInField)

variable {N : ℕ} [NeZero N]

omit [NeZero N] in
theorem period_mem_strictPeriods : (N : ℝ) ∈ ((Gamma N).map (mapGL ℝ)).strictPeriods := by
  simp only [CongruenceSubgroup.strictPeriods_Gamma]
  exact AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩

theorem period_pos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N

/-- The `q`-expansion of one factor, as a power series over the coefficient field. -/
def factorSeries (v : ℤ × ℤ) (hv : Good N v) : PowerSeries (coefficientField N) :=
  PowerSeries.mk fun n =>
    ⟨(qExpansion (N : ℝ) (torsionLogDerivative N v.1 v.2)).coeff n,
      AllLevelIntegerRows.torsion_coeff_mem N v.1 v.2 hv n⟩

theorem map_factorSeries (v : ℤ × ℤ) (hv : Good N v) :
    PowerSeries.map (algebraMap (coefficientField N) ℂ) (factorSeries v hv) =
      qExpansion (N : ℝ) (torsionLogDerivative N v.1 v.2) := by
  ext n
  rw [PowerSeries.coeff_map, factorSeries, PowerSeries.coeff_mk]
  rfl

/-- The product of the factor series. -/
def productSeries {k : ℕ} (v : Fin k → ℤ × ℤ) (hv : ∀ i, Good N (v i)) :
    PowerSeries (coefficientField N) :=
  ∏ i, factorSeries (v i) (hv i)

theorem qExpansion_principalForm (a b : ℤ) (h : Good N (a, b)) :
    qExpansion (N : ℝ) (principalForm N (NeZero.pos N) a b h) =
      qExpansion (N : ℝ) (torsionLogDerivative N a b) := rfl

/-- The expansion of the product form is the image of the product series. -/
theorem qExpansion_productForm :
    ∀ (k : ℕ) (v : Fin k → ℤ × ℤ) (hv : ∀ i, Good N (v i)),
      qExpansion (N : ℝ) (productForm N (NeZero.pos N) k v hv) =
        PowerSeries.map (algebraMap (coefficientField N) ℂ) (productSeries v hv)
  | 0, v, hv => by
    rw [productSeries, Finset.univ_eq_empty, Finset.prod_empty, map_one]
    change qExpansion (N : ℝ) (1 : ModularForm ((Gamma N).map (mapGL ℝ)) 0) = 1
    exact ModularForm.qExpansion_one
  | k + 1, v, hv => by
    change qExpansion (N : ℝ) ((principalForm N (NeZero.pos N) (v 0).1 (v 0).2 (hv 0)).mul
        (productForm N (NeZero.pos N) k (Fin.tail v) (fun i => hv i.succ))) = _
    rw [ModularForm.qExpansion_mul period_pos period_mem_strictPeriods,
      qExpansion_productForm k (Fin.tail v) (fun i => hv i.succ), productSeries,
      Fin.prod_univ_succ, map_mul, map_factorSeries, qExpansion_principalForm]
    rfl

/-- **(i) Coefficient field.** Every period-`N` coefficient of the product form lies in
`coefficientField N`. -/
theorem productForm_coeff_mem (k : ℕ) (v : Fin k → ℤ × ℤ) (hv : ∀ i, Good N (v i)) (n : ℕ) :
    (qExpansion (N : ℝ) (productForm N (NeZero.pos N) k v hv)).coeff n ∈ coefficientField N := by
  rw [qExpansion_productForm, PowerSeries.coeff_map]
  exact ((productSeries v hv).coeff n).property

/-- The transformed labels `(a, t b)`. -/
def deltaTuple (t : ℤ) {k : ℕ} (v : Fin k → ℤ × ℤ) : Fin k → ℤ × ℤ :=
  fun i => ((v i).1, t * (v i).2)

theorem deltaTuple_good (t : ℤ) {k : ℕ} {v : Fin k → ℤ × ℤ} (hv : ∀ i, Good N (v i))
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) : ∀ i, Good N (deltaTuple t v i) := fun i =>
  AllLevelIntegerRows.transformed_good N (v i).1 (v i).2 t (hv i) σ hσ

theorem map_factorSeries_galois (t : ℤ) (v : ℤ × ℤ) (hv : Good N v)
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) (hv' : Good N (v.1, t * v.2)) :
    PowerSeries.map (σ : coefficientField N →+* coefficientField N) (factorSeries v hv) =
      factorSeries (v.1, t * v.2) hv' := by
  ext n
  rw [PowerSeries.coeff_map, factorSeries, factorSeries, PowerSeries.coeff_mk,
    PowerSeries.coeff_mk]
  exact AllLevelIntegerRows.torsion_coeff_galois N v.1 v.2 t hv σ hσ n

theorem map_productSeries_galois (t : ℤ) {k : ℕ} (v : Fin k → ℤ × ℤ) (hv : ∀ i, Good N (v i))
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) :
    PowerSeries.map (σ : coefficientField N →+* coefficientField N) (productSeries v hv) =
      productSeries (deltaTuple t v) (deltaTuple_good t hv σ hσ) := by
  rw [productSeries, productSeries, map_prod]
  exact Finset.prod_congr rfl fun i _ =>
    map_factorSeries_galois t (v i) (hv i) σ hσ (deltaTuple_good t hv σ hσ i)

/-- **(ii) Galois covariance.** For `σ ζ = ζ^t`, applying `σ` to each period-`N` coefficient of
the product form gives the corresponding coefficient of the product form with labels `(a, t b)`. -/
theorem productForm_coeff_galois (t : ℤ) (k : ℕ) (v : Fin k → ℤ × ℤ) (hv : ∀ i, Good N (v i))
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) (n : ℕ) :
    ((σ ⟨(qExpansion (N : ℝ) (productForm N (NeZero.pos N) k v hv)).coeff n,
        productForm_coeff_mem k v hv n⟩ : coefficientField N) : ℂ) =
      (qExpansion (N : ℝ) (productForm N (NeZero.pos N) k (deltaTuple t v)
        (deltaTuple_good t hv σ hσ))).coeff n := by
  have hx : (⟨(qExpansion (N : ℝ) (productForm N (NeZero.pos N) k v hv)).coeff n,
      productForm_coeff_mem k v hv n⟩ : coefficientField N) = (productSeries v hv).coeff n := by
    apply Subtype.ext
    change (qExpansion (N : ℝ) (productForm N (NeZero.pos N) k v hv)).coeff n = _
    rw [qExpansion_productForm, PowerSeries.coeff_map]
    rfl
  rw [hx, qExpansion_productForm, PowerSeries.coeff_map]
  have h2 : σ ((productSeries v hv).coeff n) =
      (PowerSeries.map (σ : coefficientField N →+* coefficientField N) (productSeries v hv)).coeff n := by
    rw [PowerSeries.coeff_map]; rfl
  rw [h2, map_productSeries_galois t v hv σ hσ]
  rfl

/-- The transformed product form is again `SL(2, ℤ)`-covariant (re-export of (iii) for the
transformed labels). -/
theorem productForm_delta_slash (t : ℤ) (k : ℕ) (v : Fin k → ℤ × ℤ) (hv : ∀ i, Good N (v i))
    (σ : coefficientField N ≃ₐ[ℚ] coefficientField N)
    (hσ : σ (zetaInField N) = zetaInField N ^ t) (γ : SL(2, ℤ)) :
    ⇑(productForm N (NeZero.pos N) k (deltaTuple t v) (deltaTuple_good t hv σ hσ)) ∣[(k : ℤ)] γ =
      ⇑(productForm N (NeZero.pos N) k (fun i => ThetaFiveTorsion.act (deltaTuple t v i) γ)
        (good_act_tuple (deltaTuple_good t hv σ hσ) γ)) :=
  productForm_slash (NeZero.pos N) k _ _ γ

end ZInQ.Contrib.HeckePrimeRationality.AllLevelProducts
