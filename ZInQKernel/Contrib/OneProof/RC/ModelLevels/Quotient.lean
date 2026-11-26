import ZInQKernel.Contrib.OneProof.RC.ModelLevels.LocalLevel
import ZInQKernel.Contrib.OneProof.RC.ModelInvariants.Compatibility
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # The p-free invariant quotient from a graded unit action -/

namespace WeierstrassCurve.ModelLevels

open CategoryTheory AlgebraicGeometry ModelTorsion RC.ModelInvariants
open scoped TensorProduct

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h5 : 5 ≤ ell)
  (h : ¬ ell ∣ N * N.totient)

noncomputable instance : Algebra (LocalIntegers ell) (UniversalExactOrderAlgebra ell N h5 h) :=
  ((algebraMap (ShortBase (LocalIntegers ell)) (UniversalExactOrderAlgebra ell N h5 h)).comp
    (algebraMap (LocalIntegers ell) (ShortBase (LocalIntegers ell)))).toAlgebra

instance : IsScalarTower (LocalIntegers ell) (ShortBase (LocalIntegers ell))
    (UniversalExactOrderAlgebra ell N h5 h) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

private theorem cover_flat :
    Module.Flat (LocalIntegers ell) (UniversalExactOrderAlgebra ell N h5 h) := by
  let R := LocalIntegers ell
  letI : Module.Flat R (ShortBase R) :=
    Module.Flat.trans R (MvPolynomial (Fin 2) R) (ShortBase R)
  suffices hf : Module.Flat (ShortBase R) (UniversalExactOrderAlgebra ell N h5 h) from
    Module.Flat.trans R (ShortBase R) (UniversalExactOrderAlgebra ell N h5 h)
  let W := shortFamily R
  have hN : IsUnit (N : ShortBase R) := by
    simpa only [map_natCast] using
      (detector_units ell N h5 h).2.1.map (algebraMap R (ShortBase R))
  change Module.Flat (ShortBase R) (ExactOrderAlgebra W hN)
  letI : Module.Free (ShortBase R) (AffineTorsionAlgebra W N) :=
    (affineTorsionAlgebra_finite_etale W hN).2.1
  obtain _ | _ | N := N
  · exact inferInstanceAs (Module.Flat (ShortBase R) (ClopenFactor (exactOrderIdempotent W hN)))
  · exact inferInstanceAs (Module.Flat (ShortBase R) (ShortBase R))
  · exact inferInstanceAs (Module.Flat (ShortBase R) (ClopenFactor (exactOrderIdempotent W hN)))

variable [MulSemiringAction (ZMod N)ˣ (UniversalExactOrderAlgebra ell N h5 h)]
  [SMulCommClass (ZMod N)ˣ (LocalIntegers ell) (UniversalExactOrderAlgebra ell N h5 h)]
  (grading : ℤ → Submodule (LocalIntegers ell) (UniversalExactOrderAlgebra ell N h5 h))
  [GradedAlgebra grading] [PreservesGrading (G := (ZMod N)ˣ) grading]

/-- The candidate coordinate algebra `(S_N^H)_0`, supplied with a
grading-preserving unit action on the exact-order cover. The explicit
detector exclusions use tex 8366–8368, which permits excluding two, all
bad primes, the support of `D_wh_*`, and any other finite set. -/
noncomputable abbrev LevelQuotientAlgebra :=
  degreeZero (fixedGrading grading (ZMod N)ˣ)

/-- The p-free candidate for the open `Y₀(N)`, once the geometric action
and grading are supplied. Its short chart stabilizers are `μ₂` away from
`j = 0, 1728`, `μ₄` at 1728 and `μ₆` at 0. Their orders are prime to
`ell ≥ 5`. The explicit exclusions follow tex 8366–8368. -/
noncomputable def Y0WithGradedAction : Scheme :=
  Spec (CommRingCat.of (LevelQuotientAlgebra h5 h grading))

/-- The candidate quotient with its structure map over the detector's
local ring. The explicit tame prime exclusion uses tex 8366–8368. -/
noncomputable def Y0WithGradedActionOver : Over (Spec (CommRingCat.of (LocalIntegers ell))) :=
  Over.mk (Spec.map (CommRingCat.ofHom (S := ↥(LevelQuotientAlgebra h5 h grading))
    (algebraMap (LocalIntegers ell) (LevelQuotientAlgebra h5 h grading))))

/-- With the graded action supplied, the quotient algebra commutes with
arbitrary scalar extension by the two first-wave Reynolds retractions.
The explicit tame prime exclusion uses tex 8366–8368. -/
noncomputable def levelQuotientBaseChange [Fintype (ZMod N)ˣ]
    (B : Type*) [CommRing B] [Algebra (LocalIntegers ell) B] :
    B ⊗[LocalIntegers ell] LevelQuotientAlgebra h5 h grading ≃ₐ[B]
      degreeZero (fixedGrading (fun n => (grading n).baseChange B) (ZMod N)ˣ) :=
  fixedDegreeZeroBaseChange grading B
    (by simpa only [Nat.card_eq_fintype_card] using (detector_units ell N h5 h).2.2)

/-- Flatness of the candidate quotient with the graded action supplied.
The two retractions split off the invariant factors as modules. The tame
prime exclusion uses tex 8366–8368. -/
theorem levelQuotient_flat [Fintype (ZMod N)ˣ] :
    Module.Flat (LocalIntegers ell) (LevelQuotientAlgebra h5 h grading) := by
  letI := cover_flat h5 h
  letI := fixedPoints_flat (S := UniversalExactOrderAlgebra ell N h5 h) (G := (ZMod N)ˣ)
    (by simpa only [Nat.card_eq_fintype_card] using (detector_units ell N h5 h).2.2)
  let gr := fixedGrading grading (ZMod N)ˣ
  apply Module.Flat.of_retract (degreeZero gr).val.toLinearMap
    ((degreeZeroProjection gr).restrictScalars (LocalIntegers ell))
  exact LinearMap.ext fun x => degreeZeroProjection_fixed gr x

#print axioms cover_flat
#print axioms Y0WithGradedAction
#print axioms Y0WithGradedActionOver
#print axioms levelQuotientBaseChange
#print axioms levelQuotient_flat

end WeierstrassCurve.ModelLevels
