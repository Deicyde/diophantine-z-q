import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.RationalPoints
import ZInQKernel.HDecomp.ModCurves.Defs

/-! # Naturality of a marked lift over the generic field -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

open LeafModCurves ModelGeneric ModelTorsion Affine

open private rationalLevel_isUnit from ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational
open private exactOrderPointOfGenerator_coordinates exactOrderPointOfGenerator_coefficients from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels3.ExactOrderScaling

variable (A : WeierstrassCurve Qj) [A.IsElliptic] [(A.baseChange Kbar).IsShortNF]
  (σ : Kbar ≃ₐ[Qj] Kbar)

private theorem coefficientPoint_fixed (a : ShortBase ℚ) :
    σ (shortCoefficientPoint (R := ℚ) (A.baseChange Kbar) a) =
      shortCoefficientPoint (R := ℚ) (A.baseChange Kbar) a := by
  let c := shortCoefficientPoint (R := ℚ) (A.baseChange Kbar)
  let ρ := σ.toAlgHom.restrictScalars ℚ
  suffices ρ.comp c = c by exact DFunLike.congr_fun this a
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (shortEquation ℚ).Δ)
  let i := IsScalarTower.toAlgHom ℚ (MvPolynomial (Fin 2) ℚ) (ShortBase ℚ)
  change ((ρ.comp c).comp i).toRingHom = (c.comp i).toRingHom
  congr 1
  ext j
  have h := shortFamily_map_coefficientPoint (R := ℚ) (A.baseChange Kbar)
  fin_cases j
  · have h₄ := congrArg WeierstrassCurve.a₄ h
    change c (i (MvPolynomial.X 0)) = algebraMap Qj Kbar A.a₄ at h₄
    change σ (c (i (MvPolynomial.X 0))) = c (i (MvPolynomial.X 0))
    rw [h₄, σ.commutes]
  · have h₆ := congrArg WeierstrassCurve.a₆ h
    change c (i (MvPolynomial.X 1)) = algebraMap Qj Kbar A.a₆ at h₆
    change σ (c (i (MvPolynomial.X 1))) = c (i (MvPolynomial.X 1))
    rw [h₆, σ.commutes]

/-- The coordinate Galois action sends an exact generator to one of the same order. -/
noncomputable def galoisGenerator {N : ℕ}
    (P : Generators (A.baseChange Kbar).toAffine.Point N) :
    Generators (A.baseChange Kbar).toAffine.Point N :=
  ⟨Point.map (W' := A) σ.toAlgHom P.val,
    (addOrderOf_injective _ (Point.map_injective (W' := A) _) P.val).trans P.property⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- Galois commutes with the marked point of the universal rational short cover.
The coefficient point is fixed and the two marked coordinates transform by Galois. -/
theorem exactOrderPointOfGenerator_galois {n : ℕ} [NeZero (n + 2)]
    (P : Generators (A.baseChange Kbar).toAffine.Point (n + 2)) :
    exactOrderPointOfGenerator rationalLevel_isUnit (A.baseChange Kbar) (galoisGenerator A σ P) =
      (σ.toAlgHom.restrictScalars ℚ).comp
        (exactOrderPointOfGenerator rationalLevel_isUnit (A.baseChange Kbar) P) := by
  let hn := rationalLevel_isUnit (N := n + 2)
  let W := A.baseChange Kbar
  obtain ⟨p, hp⟩ := P
  cases p with
  | zero =>
    simp only [← Point.zero_def, addOrderOf_zero] at hp
    omega
  | some x y h =>
    let p : Generators W.toAffine.Point (n + 2) := ⟨Point.some x y h, hp⟩
    let q := galoisGenerator A σ p
    let f := exactOrderPointOfGenerator hn W p
    let g := exactOrderPointOfGenerator hn W q
    let ρ := σ.toAlgHom.restrictScalars ℚ
    change g = ρ.comp f
    let pre := exactOrderShortPresentation hn
    have eq : g.comp pre = (ρ.comp f).comp pre := by
      apply MvPolynomial.algHom_ext
      intro i
      have hcoeff (a : ShortBase ℚ) :
          g (algebraMap (ShortBase ℚ) _ a) = σ (f (algebraMap (ShortBase ℚ) _ a)) := by
        dsimp only [f, g]
        rw [exactOrderPointOfGenerator_coefficients, exactOrderPointOfGenerator_coefficients,
          coefficientPoint_fixed A σ]
      have hf := exactOrderPointOfGenerator_coordinates hn W h hp
      obtain ⟨hqns, hq⟩ : ∃ hqns : W.toAffine.Nonsingular (σ x) (σ y),
          q.val = Point.some (σ x) (σ y) hqns :=
        ⟨_, Point.map_some (W' := A) σ.toAlgHom h⟩
      have horder : addOrderOf (Point.some (σ x) (σ y) hqns) = n + 2 :=
        hq ▸ q.property
      have hg := exactOrderPointOfGenerator_coordinates hn W hqns horder
      change f (exactOrderX (shortFamily ℚ) hn) = x ∧
        f (exactOrderY (shortFamily ℚ) hn) = y at hf
      have hg' : g (exactOrderX (shortFamily ℚ) hn) = σ x ∧
          g (exactOrderY (shortFamily ℚ) hn) = σ y := by
        have he : q = ⟨Point.some (σ x) (σ y) hqns, horder⟩ := Subtype.ext hq
        simpa only [g, he] using hg
      change g (pre (MvPolynomial.X i)) = σ (f (pre (MvPolynomial.X i)))
      change g (MvPolynomial.aeval (exactOrderShortCoordinates hn) (MvPolynomial.X i)) = _
      simp only [pre, exactOrderShortPresentation, MvPolynomial.aeval_X]
      fin_cases i
      · exact hcoeff _
      · exact hcoeff _
      · exact hg'.1.trans (congrArg σ hf.1).symm
      · exact hg'.2.trans (congrArg σ hf.2).symm
      · exact hcoeff _
    apply AlgHom.ext
    intro s
    obtain ⟨b, rfl⟩ := exactOrderShortPresentation_surjective (R := ℚ) hn s
    exact DFunLike.congr_fun eq b

#print axioms coefficientPoint_fixed
#print axioms galoisGenerator
#print axioms exactOrderPointOfGenerator_galois

end WeierstrassCurve.ModelLevels.ModelGeneric2
