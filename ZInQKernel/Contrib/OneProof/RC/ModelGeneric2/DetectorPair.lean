import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.DetectorFibre
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.QuotientBaseChange
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.RationalPoints

/-! # Base change of the pinned cyclic-pair reading -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

open ModelGeneric ModelTorsion RC.ModelInvariants
open scoped TensorProduct

open private rationalLevel_isUnit from ZInQKernel.Contrib.OneProof.RC.ModelGeneric.Rational
open private detectorShort_domain detectorLevel_isUnit from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels2.DetectorCyclicLevel
open private detectorCoverAlgebra detectorCoverTower from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0Level
open private short_specialized exactOrderPointOfGenerator_specialized from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels3.CoverPairs
open private exactOrderPointOfGenerator_coefficients exactOrderPointOfGenerator_coordinates from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels3.ExactOrderScaling

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 60000
set_option maxRecDepth 4096

variable {k : Type*} [Field k] [DecidableEq k]

private theorem markedReading_coordinates {R : Type*} [CommRing R] [Algebra R k] {n : ℕ}
    (hn : IsUnit ((n + 2 : ℕ) : ShortBase R))
    [Algebra R (ExactOrderAlgebra (shortFamily R) hn)]
    [IsScalarTower R (ShortBase R) (ExactOrderAlgebra (shortFamily R) hn)]
    (W : WeierstrassCurve k) [W.IsShortNF] [W.IsElliptic]
    {x y : k} (hs : W.toAffine.Nonsingular x y)
    (ho : addOrderOf (Affine.Point.some x y hs) = n + 2) (i : Fin 5) :
    exactOrderPointOfGenerator hn W ⟨Affine.Point.some x y hs, ho⟩
      (exactOrderShortCoordinates hn i) = ![W.a₄, W.a₆, x, y, W.Δ⁻¹] i := by
  let c := shortCoefficientPoint (R := R) W
  have hw := shortFamily_map_coefficientPoint (R := R) W
  have hxy := exactOrderPointOfGenerator_coordinates hn W hs ho
  fin_cases i
  · exact (exactOrderPointOfGenerator_coefficients hn W _ (shortFamily R).a₄).trans
      (congrArg WeierstrassCurve.a₄ hw)
  · exact (exactOrderPointOfGenerator_coefficients hn W _ (shortFamily R).a₆).trans
      (congrArg WeierstrassCurve.a₆ hw)
  · exact hxy.1
  · exact hxy.2
  · change exactOrderPointOfGenerator hn W _ (algebraMap (ShortBase R) _
        (IsLocalization.Away.invSelf (shortEquation R).Δ)) = _
    rw [exactOrderPointOfGenerator_coefficients]
    change c (IsLocalization.Away.invSelf (shortEquation R).Δ) = W.Δ⁻¹
    apply eq_inv_of_mul_eq_one_left
    rw [← hw, map_Δ, shortFamily, map_Δ]
    change c (IsLocalization.Away.invSelf (shortEquation R).Δ) *
      c (algebraMap (MvPolynomial (Fin 2) R) (ShortBase R) (shortEquation R).Δ) = 1
    rw [mul_comm, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell)
  (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)
  [Algebra ℚ k] [Algebra (LocalIntegers ell) k] [IsScalarTower (LocalIntegers ell) ℚ k]
  [IsAlgClosed k]

/-- The rational base change retains the geometric reading of the actual integral
level quotient, by comparing the marked generator on both covers. -/
theorem detectorFibrePoints_eq_rationalPoints (x : Y0RationalAlgebra h₂ →ₐ[ℚ] k) :
    detectorFibrePoints h₅ htame h₂ (x.comp (Y0RationalBaseChange h₅ htame h₂).toAlgHom) =
      rationalPoints h₂ x := by
  obtain _ | _ | n := N
  · omega
  · omega
  let R := LocalIntegers ell
  let S := UniversalExactOrderAlgebra ell (n + 2) h₅ htame
  let L := Pinned.Y0LevelAlgebra h₅ htame h₂
  let hn := detectorLevel_isUnit h₅ htame
  let hq := rationalLevel_isUnit (N := n + 2)
  let gr := Pinned.detectorExactOrderGrading h₅ htame h₂
  letI := detectorCoverAlgebra h₅ htame
  letI := detectorCoverTower h₅ htame
  letI := detectorShort_domain h₅ htame
  letI := Pinned.detectorLevelAction h₅ htame h₂
  letI := Pinned.detectorLevelAction_comm h₅ htame h₂
  letI := Pinned.detectorExactOrderGradedAlgebra h₅ htame h₂
  letI := Pinned.detectorLevelAction_preserves h₅ htame h₂
  let e := Y0RationalBaseChange h₅ htame h₂
  let xL := (AlgHom.liftEquiv R ℚ L k).symm (x.comp e.toAlgHom)
  let δ : Sˣ := shortExactOrderDiscriminantUnit (R := R) hn
  have hd : (δ : S) ∈ gr 12 := shortExactOrderDiscriminantUnit_mem (R := R) hn
  let r (f : S →ₐ[R] k) := f.comp (Pinned.Y0LevelInclusion h₅ htame h₂)
  have lift : Function.Surjective r :=
    degreeZeroInvariants_restrict_surjective (G := (ZMod (n + 2))ˣ) gr (by decide) hd
  let f := (lift xL).choose
  have hf : r f = xL := (lift xL).choose_spec
  change (Quot.mk _ (shortCoverPair hn f) : PairClasses k (n + 2)) = rationalPoints h₂ x
  let c := (shortExactOrderPoints hn f).1
  let W := (shortFamily R).map c.toRingHom
  letI : W.IsShortNF := short_specialized c
  let P := (shortExactOrderPoints hn f).2
  let g := exactOrderPointOfGenerator hq W P
  have hread : exactOrderPointOfGenerator hn W P = f := by
    rw [exactOrderPointOfGenerator_specialized]
    exact (shortExactOrderPoints hn).symm_apply_apply f
  let eqv : ℚ ⊗[R] S ≃ₐ[ℚ] rationalCover (n + 2) := shortCoverBaseChange hn hq
  have hgf (b : S) : g (eqv ((1 : ℚ) ⊗ₜ[R] b)) = f b := by
    let gR : S →ₐ[R] k := ((g.comp eqv.toAlgHom).restrictScalars R).comp
      Algebra.TensorProduct.includeRight
    change gR b = f b
    obtain ⟨p, rfl⟩ := exactOrderShortPresentation_surjective hn b
    suffices he : gR.comp (exactOrderShortPresentation hn) =
        f.comp (exactOrderShortPresentation hn) from DFunLike.congr_fun he p
    apply MvPolynomial.algHom_ext
    intro i
    change gR (exactOrderShortPresentation hn (MvPolynomial.X i)) =
      f (exactOrderShortPresentation hn (MvPolynomial.X i))
    have hi : exactOrderShortPresentation hn (MvPolynomial.X i) =
        exactOrderShortCoordinates hn i := MvPolynomial.aeval_X _ _
    rw [hi]
    change g (eqv ((1 : ℚ) ⊗ₜ[R] exactOrderShortCoordinates hn i)) =
      f (exactOrderShortCoordinates hn i)
    rw [show eqv ((1 : ℚ) ⊗ₜ[R] exactOrderShortCoordinates hn i) =
      exactOrderShortCoordinates hq i from shortCoverBaseChange_coordinates hn hq i]
    obtain ⟨hs, hP⟩ := shortExactOrderPoints_affine hn f
    have hp : P = ⟨_, hP ▸ P.property⟩ := Subtype.ext hP
    rw [← hread]
    change exactOrderPointOfGenerator hq W P _ = exactOrderPointOfGenerator hn W P _
    rw [hp, markedReading_coordinates, markedReading_coordinates]
  have hinc : (g.comp (Y0RationalInclusion h₂)).comp e.toAlgHom = x.comp e.toAlgHom := by
    apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro b
    change g (eqv ((1 : ℚ) ⊗ₜ[R] Pinned.Y0LevelInclusion h₅ htame h₂ b)) =
      x (e ((1 : ℚ) ⊗ₜ[R] b))
    have h₂' : f (Pinned.Y0LevelInclusion h₅ htame h₂ b) = x (e ((1 : ℚ) ⊗ₜ[R] b)) :=
      DFunLike.congr_fun hf b
    exact (hgf (Pinned.Y0LevelInclusion h₅ htame h₂ b)).trans h₂'
  have hrestrict : g.comp (Y0RationalInclusion h₂) = x :=
    AlgHom.ext fun b => by
      obtain ⟨a, rfl⟩ := e.surjective b
      exact DFunLike.congr_fun hinc a
  refine Eq.trans ?_ (congrArg (rationalPoints h₂) hrestrict)
  change (Quot.mk _ (shortCoverPair hn f) : PairClasses k (n + 2)) =
    (rationalPointReading h₂).val (g.comp (Y0RationalInclusion h₂))
  rw [(rationalPointReading h₂).property, ← hread,
    shortCoverPair_marked, shortCoverPair_marked]

#print axioms markedReading_coordinates
#print axioms detectorFibrePoints_eq_rationalPoints

end WeierstrassCurve.ModelLevels.ModelGeneric2
