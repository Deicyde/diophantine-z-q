import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational
import ZInQKernel.HDecomp.ModCurves.Defs
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Flat

/-! # Faithful localization of the rational quotient at the generic j-point -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric

open ModelTorsion LeafModCurves

open private rationalLevel_isUnit from
  ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational

private theorem shortBase_aeval_j_injective :
    Function.Injective (Polynomial.aeval (shortFamily ℚ).j : Polynomial ℚ →ₐ[ℚ] ShortBase ℚ) := by
  letI := invertibleOfNonzero (by norm_num : (2 : Qj) ≠ 0)
  letI := invertibleOfNonzero (by norm_num : (3 : Qj) ≠ 0)
  let V := Ej.toShortNF • Ej
  let c := shortCoefficientPoint (R := ℚ) V
  have hc : c (shortFamily ℚ).j = RatFunc.X := by
    refine ((shortFamily ℚ).map_j c.toRingHom).symm.trans ?_
    have hv : ((shortFamily ℚ).map c.toRingHom).j = V.j := by
      simpa only [WeierstrassCurve.j_eq] using congrArg
        (fun W : WeierstrassCurve Qj => W.Δ⁻¹ * W.c₄ ^ 3)
        (shortFamily_map_coefficientPoint (R := ℚ) V)
    exact hv.trans ((variableChange_j Ej Ej.toShortNF).trans Ej_j)
  let x : Polynomial ℚ →ₐ[ℚ] Qj := IsScalarTower.toAlgHom ℚ (Polynomial ℚ) Qj
  have he : c.comp (Polynomial.aeval (shortFamily ℚ).j) = x := by
    apply Polynomial.algHom_ext
    change c (Polynomial.aeval (shortFamily ℚ).j Polynomial.X) =
      algebraMap (Polynomial ℚ) Qj Polynomial.X
    rw [Polynomial.aeval_X, RatFunc.algebraMap_X, hc]
  apply Function.Injective.of_comp (f := c)
  change Function.Injective (c.comp (Polynomial.aeval (shortFamily ℚ).j))
  rw [he]
  exact IsFractionRing.injective (Polynomial ℚ) Qj

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

set_option backward.isDefEq.respectTransparency false in
/-- The rational quotient has no torsion over the actual affine j-line.
The j-map of the short coefficient ring is dominant, as witnessed by the
short form of `Ej`. The marked cover is flat over that coefficient ring. -/
theorem Y0RationalAlgebra_j_torsionFree :
    letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
    Module.IsTorsionFree (Polynomial ℚ) (Y0RationalAlgebra h₂) := by
  let A := ShortBase ℚ
  let S := rationalCover N
  let B := Y0RationalAlgebra h₂
  let W := shortFamily ℚ
  let inc := Y0RationalInclusion h₂
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  letI : Algebra.Etale A S :=
    (exactOrderAlgebra_finite_etale W (rationalLevel_isUnit (N := N))).2
  have hinc : inc.comp (Y0RationalJMap h₂) =
      (IsScalarTower.toAlgHom ℚ A S).comp (Polynomial.aeval W.j) := by
    apply Polynomial.algHom_ext
    change inc (Polynomial.aeval (Y0RationalJ h₂) Polynomial.X) =
      algebraMap A S (Polynomial.aeval W.j Polynomial.X)
    simp only [Polynomial.aeval_X]
    rfl
  have hi : Function.Injective inc := Subtype.val_injective.comp Subtype.val_injective
  refine Module.IsTorsionFree.of_smul_eq_zero (M := B) fun f b h => ?_
  have hb := congrArg inc h
  change inc ((Y0RationalJMap h₂ f) * b) = inc 0 at hb
  rw [map_mul, map_zero] at hb
  change (inc.comp (Y0RationalJMap h₂)) f * inc b = 0 at hb
  rw [hinc] at hb
  change algebraMap A S (Polynomial.aeval W.j f) * inc b = 0 at hb
  rw [← Algebra.smul_def] at hb
  rcases smul_eq_zero.mp hb with hzero | hzero
  · exact Or.inl (map_eq_zero_iff _ shortBase_aeval_j_injective |>.mp hzero)
  · exact Or.inr (map_eq_zero_iff _ hi |>.mp hzero)

#print axioms shortBase_aeval_j_injective
#print axioms Y0RationalAlgebra_j_torsionFree

end WeierstrassCurve.ModelLevels.ModelGeneric
