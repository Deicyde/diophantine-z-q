import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Tactic

/-! The normalized-induction computation at the identity (tex 9813–9840).
The finite operator is the manuscript's sum of right translates. No Haar measure or
general theory of smooth representations is needed for its evaluation. -/

noncomputable section

namespace ZInQ.Manuscript.RC.O12Local

open Matrix

/-- An upper triangular element of the local Borel. -/
def upper {F : Type*} [Field F] (a d : Fˣ) (x : F) : GL (Fin 2) F :=
  GeneralLinearGroup.mkOfDetNeZero !![(a : F), x; 0, (d : F)] (by
    simp [det_fin_two])

variable (p : ℕ) [Fact p.Prime]

/-- The uniformizer, regarded as a unit of the field. -/
def uniformizer : ℚ_[p]ˣ := Units.mk0 (p : ℚ_[p]) (by
  exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- The representatives in the stated Haar normalization, using (0,ldots,p-1). -/
def representative (b : Fin p) : GL (Fin 2) ℚ_[p] :=
  upper (uniformizer p) 1 b.val

/-- The finite sum of right translates in tex 9833–9834. -/
def heckeSum {E : Type*} [AddCommMonoid E] (v : GL (Fin 2) ℚ_[p] → E)
    (g : GL (Fin 2) ℚ_[p]) : E :=
  ∑ b : Fin p, v (g * representative p b)

/-- Algebraic evaluation of the sum in a normalized induction model.
Only left equivariance at the displayed representatives is used in evaluating at (1);
right equivariance and support specify the choice of vector, and need not be assumed here. -/
theorem heckeSum_at_one {E : Type*} [Field E] (μ₁ μ₂ halfMod : ℚ_[p]ˣ →* Eˣ)
    (v : GL (Fin 2) ℚ_[p] → E)
    (hv : ∀ a d x g, v (upper a d x * g) =
      (μ₁ a : E) * (μ₂ d : E) * (halfMod (a / d) : E) * v g) :
    heckeSum p v 1 = (p : E) * (μ₁ (uniformizer p) : E) *
      (halfMod (uniformizer p) : E) * v 1 := by
  have ht (b : Fin p) : v (representative p b) =
      (μ₁ (uniformizer p) : E) * (halfMod (uniformizer p) : E) * v 1 := by
    simpa [representative] using hv (uniformizer p) 1 (b.val : ℚ_[p]) 1
  simp only [heckeSum, one_mul, ht, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The manuscript's numerical coefficient in the complex unitary normalization.
In particular, for its lower-right (K_0(p))-equivariant vector supported on (BK_0(p))
and normalized by (v(1)=1), the value is (sqrt p,mu_1(p)). -/
theorem newvector_at_one (μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ)
    (v : GL (Fin 2) ℚ_[p] → ℂ)
    (hv : ∀ a d x g, v (upper a d x * g) =
      (μ₁ a : ℂ) * (μ₂ d : ℂ) * (Real.sqrt ‖(a : ℚ_[p]) / (d : ℚ_[p])‖ : ℂ) * v g)
    (h₁ : v 1 = 1) :
    heckeSum p v 1 = (Real.sqrt (p : ℝ) : ℂ) * (μ₁ (uniformizer p) : ℂ) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hs : (Real.sqrt (p : ℝ) : ℂ) ^ 2 = (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg p : (0 : ℝ) ≤ (p : ℝ))
  have hs' : (Real.sqrt (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_ne_zero'.2 (lt_of_le_of_ne (Nat.cast_nonneg p) hp.symm))
  have hterm (b : Fin p) :
      v (representative p b) =
        (μ₁ (uniformizer p) : ℂ) * (Real.sqrt (p : ℝ) : ℂ)⁻¹ := by
    have e := hv (uniformizer p) 1 (b.val : ℚ_[p]) 1
    simpa [representative, h₁, uniformizer, Padic.norm_p, Real.sqrt_inv] using e
  simp only [heckeSum, one_mul, hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← hs]
  field_simp

/-- In any realization of the same half-modulus, (pcdot p^{-1/2}=p^{1/2}).
The choice of half-modulus fixes which square root occurs. -/
theorem heckeSum_at_one_normalized {E : Type*} [Field E] (μ₁ μ₂ halfMod : ℚ_[p]ˣ →* Eˣ)
    (hhalf : (p : E) * (halfMod (uniformizer p) : E) ^ 2 = 1)
    (v : GL (Fin 2) ℚ_[p] → E)
    (hv : ∀ a d x g, v (upper a d x * g) =
      (μ₁ a : E) * (μ₂ d : E) * (halfMod (a / d) : E) * v g) :
    heckeSum p v 1 =
      ((halfMod (uniformizer p))⁻¹ : Eˣ).val * (μ₁ (uniformizer p) : E) * v 1 := by
  have hne := (halfMod (uniformizer p)).ne_zero
  have h : (p : E) * (halfMod (uniformizer p) : E) =
      (halfMod (uniformizer p) : E)⁻¹ := by
    rw [← one_div]
    apply (eq_div_iff hne).2
    simpa [pow_two, mul_assoc] using hhalf
  rw [heckeSum_at_one p μ₁ μ₂ halfMod v hv, Units.val_inv_eq_inv_val, ← h]
  ring

#print axioms heckeSum_at_one
#print axioms newvector_at_one
#print axioms heckeSum_at_one_normalized

end ZInQ.Manuscript.RC.O12Local
