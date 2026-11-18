import Mathlib.NumberTheory.ModularForms.LFunction
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Critical Mellin functionals and finite character averaging

The Mellin integrals below are convergent integrals of actual cusp forms.
Their linear maps agree with the completed and ordinary modular L-functions
at every complex argument. No pointwise nonvanishing is assumed.
-/

noncomputable section

open Complex MeasureTheory Filter
open UpperHalfPlane hiding I
open scoped Topology Classical

namespace CriticalTwists

section Mellin

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] [Γ.HasDetOne]
variable {k : ℤ}

/-- Cuspidality supplies convergence at every argument, including critical ones. -/
theorem cuspMellin_convergent (hk : 0 < k) (f : CuspForm Γ k) (s : ℂ) :
    MellinConvergent (fun t : ℝ => f (ofComplex (I * t))) s :=
  ((CuspForm.isStrongFEPair hk f).hasMellin s).1

/-- The actual Mellin integral, as a linear functional on cusp forms. -/
def completedMellinLinear (hk : 0 < k) (s : ℂ) : CuspForm Γ k →ₗ[ℂ] ℂ where
  toFun f := mellin (fun t : ℝ => f (ofComplex (I * t))) s
  map_add' f g := by
    simpa only [FunLike.coe_add, Pi.add_apply] using
      (hasMellin_add (cuspMellin_convergent hk f s) (cuspMellin_convergent hk g s)).2
  map_smul' c f := by
    simpa only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using
      mellin_const_smul (fun t : ℝ => f (ofComplex (I * t))) s c

/-- The integral is the existing completed L-function, not a new continuation. -/
theorem completedMellinLinear_apply (hk : 0 < k) (s : ℂ) (f : CuspForm Γ k) :
    completedMellinLinear hk s f = ModularForm.Λ hk f s := by
  change mellin (fun t : ℝ => f (ofComplex (I * t))) s = ModularForm.Λ hk f s
  exact congrFun (CuspForm.Λ_eq_mellin hk f).symm s

/-- The ordinary L-value functional at a fixed complex argument. -/
def LValueLinear (hk : 0 < k) (s : ℂ) : CuspForm Γ k →ₗ[ℂ] ℂ :=
  (2 / Gammaℂ s) • completedMellinLinear hk s

/-- This functional is bound to the existing modular L-value at every argument. -/
theorem LValueLinear_apply (hk : 0 < k) (s : ℂ) (f : CuspForm Γ k) :
    LValueLinear hk s f = ModularForm.L hk f s := by
  simp only [LValueLinear, LinearMap.smul_apply, smul_eq_mul, completedMellinLinear_apply,
    ModularForm.L]
  ring

/-- Critical argument one is an unweighted, convergent Mellin integral. -/
theorem L_one_eq_integral (hk : 0 < k) (f : CuspForm Γ k) :
    ModularForm.L hk f 1 = (2 * Real.pi : ℂ) *
      ∫ t : ℝ in Set.Ioi 0, f (ofComplex (I * t)) := by
  rw [ModularForm.L, CuspForm.Λ_eq_mellin]
  simp only [mellin, sub_self, cpow_zero, one_smul]
  have hc : 2 / Gammaℂ (1 : ℂ) = (2 * Real.pi : ℂ) := by
    simp only [Gammaℂ, Gamma_one, mul_one, cpow_neg, cpow_one]
    field_simp
  rw [hc]
  ring

/-- Critical argument two is a convergent first-moment Mellin integral. -/
theorem L_two_eq_integral (hk : 0 < k) (f : CuspForm Γ k) :
    ModularForm.L hk f 2 = (2 * Real.pi : ℂ) ^ 2 *
      ∫ t : ℝ in Set.Ioi 0, (t : ℂ) * f (ofComplex (I * t)) := by
  rw [ModularForm.L, CuspForm.Λ_eq_mellin]
  have he : (2 : ℂ) - 1 = 1 := by norm_num
  simp only [mellin, he, cpow_one, smul_eq_mul]
  have hg : Gamma (2 : ℂ) = 1 := by
    simpa using Gamma_nat_eq_factorial 1
  have hc : 2 / Gammaℂ (2 : ℂ) = (2 * Real.pi : ℂ) ^ 2 := by
    simp only [Gammaℂ, hg, mul_one, cpow_neg]
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) from rfl, cpow_natCast]
    field_simp
  rw [hc]
  ring

end Mellin

section FiniteCharacters

variable {M : ℕ} [NeZero M]

/-- The indicator of one residue class, regarded as a complex coefficient multiplier. -/
def residueIndicator (u : ZMod M) : ZMod M → ℂ := fun b => if b = u then 1 else 0

/-- Character orthogonality reconstructs a unit-supported residue indicator. -/
theorem characterExpansion (u : ZMod M) (hu : IsUnit u) :
    (M.totient : ℂ) • residueIndicator u =
      ∑ ψ : DirichletCharacter ℂ M, ψ u⁻¹ • (ψ : ZMod M → ℂ) := by
  ext b
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu b]
  simp only [residueIndicator]
  by_cases h : b = u
  · simp [h]
  · simp [h, Ne.symm h]

/-- Projection onto one of the two eigenspaces of negation. -/
def parityProjection (ε : ℂ) : (ZMod M → ℂ) →ₗ[ℂ] (ZMod M → ℂ) where
  toFun Φ b := (Φ b + ε * Φ (-b)) / 2
  map_add' Φ Ψ := by
    ext b
    simp only [Pi.add_apply]
    ring
  map_smul' c Φ := by
    ext b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Negation sends the indicator at `u` to the indicator at `-u`. -/
theorem residueIndicator_neg (u b : ZMod M) :
    residueIndicator u (-b) = residueIndicator (-u) b := by
  simp only [residueIndicator]
  have h : -b = u ↔ b = -u := by rw [neg_eq_iff_eq_neg]
  simp only [h]

/-- The projected residue multiplier is an explicit signed pair of indicators. -/
theorem parityProjection_residueIndicator (ε : ℂ) (u : ZMod M) :
    parityProjection ε (residueIndicator u) =
      (2 : ℂ)⁻¹ • (residueIndicator u + ε • residueIndicator (-u)) := by
  ext b
  simp only [parityProjection, LinearMap.coe_mk, AddHom.coe_mk, residueIndicator_neg,
    Pi.smul_apply, Pi.add_apply, smul_eq_mul]
  ring

/-- Even projection keeps exactly the even Dirichlet characters. -/
theorem evenProjection_character (ψ : DirichletCharacter ℂ M) :
    parityProjection 1 (ψ : ZMod M → ℂ) = if ψ.Even then (ψ : ZMod M → ℂ) else 0 := by
  rcases ψ.even_or_odd with he | ho
  · ext b
    simp [parityProjection, he, he.eval_neg]
  · ext b
    simp [parityProjection, ho.not_even, ho.eval_neg]

/-- Odd projection keeps exactly the odd Dirichlet characters. -/
theorem oddProjection_character (ψ : DirichletCharacter ℂ M) :
    parityProjection (-1) (ψ : ZMod M → ℂ) = if ψ.Odd then (ψ : ZMod M → ℂ) else 0 := by
  rcases ψ.even_or_odd with he | ho
  · ext b
    simp [parityProjection, he.not_odd, he.eval_neg]
  · ext b
    simp [parityProjection, ho, ho.eval_neg]

/-- Signed residue reconstruction using only even characters. -/
theorem evenCharacterExpansion (u : ZMod M) (hu : IsUnit u) :
    ((M.totient : ℂ) / 2) • (residueIndicator u + residueIndicator (-u)) =
      ∑ ψ : DirichletCharacter ℂ M,
        if ψ.Even then ψ u⁻¹ • (ψ : ZMod M → ℂ) else 0 := by
  have h := congrArg (parityProjection (M := M) 1) (characterExpansion u hu)
  simpa only [map_smul, map_sum, parityProjection_residueIndicator, evenProjection_character,
    one_smul, smul_smul, smul_ite, smul_zero, div_eq_mul_inv] using h

/-- Signed residue reconstruction using only odd characters. -/
theorem oddCharacterExpansion (u : ZMod M) (hu : IsUnit u) :
    ((M.totient : ℂ) / 2) • (residueIndicator u - residueIndicator (-u)) =
      ∑ ψ : DirichletCharacter ℂ M,
        if ψ.Odd then ψ u⁻¹ • (ψ : ZMod M → ℂ) else 0 := by
  have h := congrArg (parityProjection (M := M) (-1)) (characterExpansion u hu)
  simpa only [map_smul, map_sum, parityProjection_residueIndicator, oddProjection_character,
    neg_one_smul, smul_smul, smul_ite, smul_zero, div_eq_mul_inv, sub_eq_add_neg] using h

/-- Every complex linear functional has the exact even-character average. -/
theorem evenCharacterAverage (T : (ZMod M → ℂ) →ₗ[ℂ] ℂ) (u : ZMod M) (hu : IsUnit u) :
    (M.totient : ℂ) / 2 * T (residueIndicator u + residueIndicator (-u)) =
      ∑ ψ : DirichletCharacter ℂ M,
        if ψ.Even then ψ u⁻¹ * T (ψ : ZMod M → ℂ) else 0 := by
  have h := congrArg T (evenCharacterExpansion u hu)
  simp only [map_smul, map_sum, smul_eq_mul] at h
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro ψ hψ
  split_ifs <;> simp [map_smul, smul_eq_mul]

/-- Every complex linear functional has the exact odd-character average. -/
theorem oddCharacterAverage (T : (ZMod M → ℂ) →ₗ[ℂ] ℂ) (u : ZMod M) (hu : IsUnit u) :
    (M.totient : ℂ) / 2 * T (residueIndicator u - residueIndicator (-u)) =
      ∑ ψ : DirichletCharacter ℂ M,
        if ψ.Odd then ψ u⁻¹ * T (ψ : ZMod M → ℂ) else 0 := by
  have h := congrArg T (oddCharacterExpansion u hu)
  simp only [map_smul, map_sum, smul_eq_mul] at h
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro ψ hψ
  split_ifs <;> simp [map_smul, smul_eq_mul]

end FiniteCharacters

end CriticalTwists
