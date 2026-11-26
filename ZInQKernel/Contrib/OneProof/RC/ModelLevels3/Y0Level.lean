import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.ShortLevelAction
import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.DetectorCyclicLevel
import ZInQKernel.Contrib.OneProof.RC.ModelLevels.Quotient
import Batteries.Tactic.OpenPrivate

/-! # The pinned integral degree-zero quotient -/

namespace WeierstrassCurve.ModelLevels.Pinned

open CategoryTheory AlgebraicGeometry ModelTorsion RC.ModelInvariants
open scoped TensorProduct

open private detectorShort_domain detectorLevel_isUnit from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels2.DetectorCyclicLevel

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell)
  (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)

private noncomputable def detectorCoverAlgebra {n : ℕ} [NeZero (n + 2)]
    (htame : ¬ ell ∣ (n + 2) * (n + 2).totient) :
    Algebra (LocalIntegers ell)
      (ExactOrderAlgebra (shortFamily (LocalIntegers ell)) (detectorLevel_isUnit h₅ htame)) :=
  inferInstanceAs (Algebra (LocalIntegers ell) (UniversalExactOrderAlgebra ell (n + 2) h₅ htame))

private theorem detectorCoverTower {n : ℕ} [NeZero (n + 2)]
    (htame : ¬ ell ∣ (n + 2) * (n + 2).totient) :
    letI := detectorCoverAlgebra h₅ htame
    IsScalarTower (LocalIntegers ell) (ShortBase (LocalIntegers ell))
      (ExactOrderAlgebra (shortFamily (LocalIntegers ell)) (detectorLevel_isUnit h₅ htame)) :=
  inferInstanceAs (IsScalarTower (LocalIntegers ell) (ShortBase (LocalIntegers ell))
    (UniversalExactOrderAlgebra ell (n + 2) h₅ htame))

/-- The grading on the universal exact-order cover is defined by the
five coordinate weights. -/
noncomputable def detectorExactOrderGrading :
    ℤ → Submodule (LocalIntegers ell) (UniversalExactOrderAlgebra ell N h₅ htame) := by
  obtain _ | _ | n := N
  · omega
  · omega
  · letI := detectorCoverAlgebra h₅ htame
    exact shortExactOrderGrading (R := LocalIntegers ell) (n := n) (detectorLevel_isUnit h₅ htame)

/-- The weighted components give an internal grading at the detector. -/
@[instance_reducible] noncomputable def detectorExactOrderGradedAlgebra :
    GradedAlgebra (detectorExactOrderGrading h₅ htame h₂) := by
  obtain _ | _ | n := N
  · omega
  · omega
  · letI := detectorCoverAlgebra h₅ htame
    letI := detectorCoverTower h₅ htame
    letI := detectorShort_domain h₅ htame
    exact shortExactOrderGradedAlgebra (R := LocalIntegers ell) (n := n)
      (detectorLevel_isUnit h₅ htame)

/-- The pinned level action on the exact-order algebra of the whole
short Weierstrass locus. -/
@[instance_reducible] noncomputable def detectorLevelAction :
    MulSemiringAction (ZMod N)ˣ (UniversalExactOrderAlgebra ell N h₅ htame) :=
  letI := detectorShort_domain h₅ htame
  levelSemiringAction _ (detectorLevel_isUnit h₅ htame) h₂

theorem detectorLevelAction_comm :
    letI := detectorLevelAction h₅ htame h₂
    SMulCommClass (ZMod N)ˣ (LocalIntegers ell) (UniversalExactOrderAlgebra ell N h₅ htame) := by
  letI := detectorLevelAction h₅ htame h₂
  letI := detectorShort_domain h₅ htame
  refine ⟨fun g r x => ?_⟩
  let e := levelUnitAut (shortFamily (LocalIntegers ell)) (detectorLevel_isUnit h₅ htame) h₂ g
  let S := UniversalExactOrderAlgebra ell N h₅ htame
  let f : S ≃ₐ[ShortBase (LocalIntegers ell)] S := e
  exact (f.restrictScalars (LocalIntegers ell)).toAlgHom.toLinearMap.map_smul r x

theorem detectorLevelAction_preserves :
    letI := detectorLevelAction h₅ htame h₂
    letI := detectorLevelAction_comm h₅ htame h₂
    letI := detectorExactOrderGradedAlgebra h₅ htame h₂
    PreservesGrading (G := (ZMod N)ˣ) (detectorExactOrderGrading h₅ htame h₂) := by
  obtain _ | _ | n := N
  · omega
  · omega
  · letI := detectorCoverAlgebra h₅ htame
    letI := detectorCoverTower h₅ htame
    letI := detectorShort_domain h₅ htame
    letI := detectorLevelAction h₅ htame h₂
    letI := detectorLevelAction_comm h₅ htame h₂
    letI := detectorExactOrderGradedAlgebra h₅ htame h₂
    refine ⟨fun a i x hx => ?_⟩
    exact shortLevelUnitAut_mem (R := LocalIntegers ell) (detectorLevel_isUnit h₅ htame) a hx

/-- The coordinate algebra of the pinned short quotient. The finite
invariants are `DetectorCyclicLevelAlgebra` with scalars restricted to
`ℤ_(ell)`. These are formed over the whole short Weierstrass locus,
where scaling moves both coefficients. The tame exclusions use tex
8366–8368. -/
noncomputable abbrev Y0LevelAlgebra :=
  letI := detectorLevelAction h₅ htame h₂
  letI := detectorLevelAction_comm h₅ htame h₂
  letI := detectorExactOrderGradedAlgebra h₅ htame h₂
  letI := detectorLevelAction_preserves h₅ htame h₂
  LevelQuotientAlgebra h₅ htame (detectorExactOrderGrading h₅ htame h₂)

/-- The affine quotient with its structure map over the detector ring.
It takes degree zero on the universal `DetectorCyclicLevelAlgebra` over
the whole short locus. The tame exclusions use tex 8366–8368. -/
noncomputable def Y0Level : Over (Spec (CommRingCat.of (LocalIntegers ell))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (S := ↥(Y0LevelAlgebra h₅ htame h₂))
    (algebraMap (LocalIntegers ell) (Y0LevelAlgebra h₅ htame h₂))))

/-- Both quotient operations for the pinned algebra commute with
arbitrary scalar extension, including the detector's residue field. -/
noncomputable def levelQuotientBaseChange (B : Type*) [CommRing B] [Algebra (LocalIntegers ell) B] :
    letI := detectorLevelAction h₅ htame h₂
    letI := detectorLevelAction_comm h₅ htame h₂
    letI := detectorExactOrderGradedAlgebra h₅ htame h₂
    letI := detectorLevelAction_preserves h₅ htame h₂
    B ⊗[LocalIntegers ell] Y0LevelAlgebra h₅ htame h₂ ≃ₐ[B]
      degreeZero (fixedGrading (fun i => (detectorExactOrderGrading h₅ htame h₂ i).baseChange B)
        (ZMod N)ˣ) := by
  letI := detectorLevelAction h₅ htame h₂
  letI := detectorLevelAction_comm h₅ htame h₂
  letI := detectorExactOrderGradedAlgebra h₅ htame h₂
  letI := detectorLevelAction_preserves h₅ htame h₂
  exact ModelLevels.levelQuotientBaseChange h₅ htame (detectorExactOrderGrading h₅ htame h₂) B

/-- Flatness of the pinned quotient over the detector's local integers. -/
theorem levelQuotient_flat :
    Module.Flat (LocalIntegers ell) (Y0LevelAlgebra h₅ htame h₂) := by
  letI := detectorLevelAction h₅ htame h₂
  letI := detectorLevelAction_comm h₅ htame h₂
  letI := detectorExactOrderGradedAlgebra h₅ htame h₂
  letI := detectorLevelAction_preserves h₅ htame h₂
  exact ModelLevels.levelQuotient_flat h₅ htame (detectorExactOrderGrading h₅ htame h₂)

#print axioms detectorCoverAlgebra
#print axioms detectorCoverTower
#print axioms detectorExactOrderGrading
#print axioms detectorExactOrderGradedAlgebra
#print axioms detectorLevelAction
#print axioms detectorLevelAction_comm
#print axioms detectorLevelAction_preserves
#print axioms Y0LevelAlgebra
#print axioms Y0Level
#print axioms levelQuotientBaseChange
#print axioms levelQuotient_flat

end WeierstrassCurve.ModelLevels.Pinned
