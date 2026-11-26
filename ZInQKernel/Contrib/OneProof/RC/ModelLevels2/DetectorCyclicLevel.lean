import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.CyclicLevel
import ZInQKernel.Contrib.OneProof.RC.ModelLevels.LocalLevel
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-! # The finite part of the quotient at the detector -/

namespace WeierstrassCurve.ModelLevels

open ModelTorsion

private theorem shortDiscriminant_ne_zero (R : Type*) [CommRing R] (h : (64 : R) ≠ 0) :
    (shortEquation R).Δ ≠ 0 := by
  let f : MvPolynomial (Fin 2) R →ₐ[R] R := MvPolynomial.aeval (fun i => if i = 0 then 1 else 0)
  let W := (shortEquation R).map f.toRingHom
  haveI : W.IsShortNF := ⟨by simp [W, shortEquation], by simp [W, shortEquation],
    by simp [W, shortEquation]⟩
  have hΔ : W.Δ = -(64 : R) := by
    rw [Δ_of_isShortNF]
    norm_num [W, shortEquation, f]
  intro hz
  change ((shortEquation R).map f.toRingHom).Δ = _ at hΔ
  rw [map_Δ, hz, map_zero, eq_comm, neg_eq_zero] at hΔ
  exact h hΔ

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell)
  (htame : ¬ ell ∣ N * N.totient)

include h₅ htame in
private theorem detectorShort_domain : IsDomain (ShortBase (LocalIntegers ell)) := by
  have h₆ := (detector_units ell N h₅ htame).1
  have h₂ : IsUnit (2 : LocalIntegers ell) :=
    isUnit_of_dvd_unit (show (2 : LocalIntegers ell) ∣ 6 from ⟨3, by norm_num⟩) h₆
  have h64 : (64 : LocalIntegers ell) ≠ 0 := by
    rw [show (64 : LocalIntegers ell) = 2 ^ 6 by norm_num]
    exact pow_ne_zero _ h₂.ne_zero
  exact Localization.Away.isDomain (shortDiscriminant_ne_zero _ h64)

include h₅ htame in
private theorem detectorLevel_isUnit : IsUnit (N : ShortBase (LocalIntegers ell)) := by
  simpa only [map_natCast] using
    (detector_units ell N h₅ htame).2.1.map
      (algebraMap (LocalIntegers ell) (ShortBase (LocalIntegers ell)))

/-- The geometric unit invariants of the universal exact-order cover
at detector level. The tame prime exclusions use tex 8366–8368. -/
noncomputable abbrev DetectorCyclicLevelAlgebra (h₂ : 2 ≤ N) :
    Subalgebra (ShortBase (LocalIntegers ell)) (UniversalExactOrderAlgebra ell N h₅ htame) :=
  letI := detectorShort_domain h₅ htame
  CyclicLevelAlgebra (shortFamily (LocalIntegers ell)) (detectorLevel_isUnit h₅ htame) h₂

/-- Over each algebraically closed field and chosen short coefficient
point, the geometric unit invariants parametrize the cyclic subgroups of
the specialized curve. This includes the algebraic closure of the
detector's residue field. -/
noncomputable def detectorCyclicLevelPoints (h₂ : 2 ≤ N) {k : Type*} [Field k]
    [DecidableEq k] [IsAlgClosed k] [Algebra (ShortBase (LocalIntegers ell)) k] :
    (DetectorCyclicLevelAlgebra h₅ htame h₂ →ₐ[ShortBase (LocalIntegers ell)] k) ≃
      CyclicSubgroups ((shortFamily (LocalIntegers ell)).map
        (algebraMap (ShortBase (LocalIntegers ell)) k)).toAffine.Point N := by
  letI := detectorShort_domain h₅ htame
  apply cyclicLevelPoints
  have hu := (detector_units ell N h₅ htame).2.2.map
    (algebraMap (LocalIntegers ell) (ShortBase (LocalIntegers ell)))
  simpa only [map_natCast, Nat.card_eq_fintype_card] using hu

#print axioms shortDiscriminant_ne_zero
#print axioms detectorShort_domain
#print axioms detectorLevel_isUnit
#print axioms DetectorCyclicLevelAlgebra
#print axioms detectorCyclicLevelPoints

end WeierstrassCurve.ModelLevels
