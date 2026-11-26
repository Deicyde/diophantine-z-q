module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

public section

/-! The tangent polynomial used by the local Euler factor is independent,
up to affine substitution and nonzero scaling, of Weierstrass coordinates. -/

namespace ZInQ.Manuscript.RankModel

open Polynomial WeierstrassCurve

noncomputable def tangentPolynomial {R : Type*} [CommRing R] (W : WeierstrassCurve R) : R[X] :=
  C W.c₄ * X ^ 2 + C (W.a₁ * W.c₄) * X - C (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄)

@[simp] private theorem map_tangentPolynomial {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (W : WeierstrassCurve R) :
    (tangentPolynomial W).map f = tangentPolynomial (W.map f) := by
  simp [tangentPolynomial, map_ofNat]

private theorem tangentPolynomial_smul {F : Type*} [Field F]
    (W : WeierstrassCurve F) (U : VariableChange F) :
    tangentPolynomial (U • W) = C ((↑U.u⁻¹ : F) ^ 6) *
      (tangentPolynomial W).comp (C (U.u : F) * X + C U.s) := by
  have hh := (show (↑U.u⁻¹ : F) * (U.u : F) = 1 by simp)
  have hu : C (↑U.u⁻¹ : F) * C (U.u : F) = (1 : F[X]) := by rw [← C_mul, hh, C_1]
  simp only [tangentPolynomial, variableChange_a₁, variableChange_a₂,
    variableChange_b₂, variableChange_b₄, variableChange_b₆, c₄, add_comp, sub_comp, mul_comp,
    pow_comp, C_comp, X_comp, map_mul, map_add, map_sub, map_pow, map_ofNat, ofNat_comp]
  have hup : C (↑U.u⁻¹ : F) ^ 2 * C (U.u : F) ^ 2 = (1 : F[X]) := by
    rw [← mul_pow, hu, one_pow]
  -- Keep the unit cancellation outside polynomial normalization.
  linear_combination
    -(C (↑U.u⁻¹ : F) ^ 4 * (C W.b₂ ^ 2 - 24 * C W.b₄) * X ^ 2) * hup -
    (C (↑U.u⁻¹ : F) ^ 5 * (C W.b₂ ^ 2 - 24 * C W.b₄) * (C W.a₁ + 2 * C U.s) * X) * hu

private theorem splits_tangentPolynomial_smul_iff {F : Type*} [Field F]
    (W : WeierstrassCurve F) (U : VariableChange F) :
    (tangentPolynomial (U • W)).Splits ↔ (tangentPolynomial W).Splits := by
  rw [tangentPolynomial_smul, splits_mul_iff_right (by simp) (Splits.C _)]
  symm
  apply splits_iff_comp_splits_of_natDegree_eq_one
  rw [natDegree_add_C, natDegree_C_mul (Units.ne_zero U.u), natDegree_X]

/-- Read the splitting clause of a minimal local equation on its actual
residue curve. The assertion concerns the literal tangent polynomial in
Mathlib's definition, also in residue characteristics two and three. -/
theorem hasSplitMultiplicativeReduction_iff_residue {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve K) [IsMinimal R W] :
    HasSplitMultiplicativeReduction R W ↔
      HasMultiplicativeReduction R W ∧ (tangentPolynomial (W.reduction R)).Splits := by
  rw [hasSplitMultiplicativeReduction_iff]
  change (∃ _ : HasMultiplicativeReduction R W,
    ((tangentPolynomial (W.integralModel R)).map (IsLocalRing.residue R)).Splits) ↔ _
  rw [map_tangentPolynomial]
  exact exists_prop

/-- The splitting test is invariant under the actual residue variable change. -/
theorem residueSplit_iff_of_variableChange {R K : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {W W' : WeierstrassCurve K}
    [IsMinimal R W] [IsMinimal R W']
    (h : ∃ U : VariableChange (IsLocalRing.ResidueField R), W'.reduction R = U • W.reduction R) :
    (tangentPolynomial (W'.reduction R)).Splits ↔ (tangentPolynomial (W.reduction R)).Splits := by
  obtain ⟨U, hU⟩ := h
  rw [hU, splits_tangentPolynomial_smul_iff]

end ZInQ.Manuscript.RankModel
