import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.NormalRetract
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelReducedFibres
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelSmoothCriterion
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.RegularLocalRing.UniqueFactorization
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Localization.BaseChange

/-! # Smoothness of the pinned integral quotient -/

namespace WeierstrassCurve.ModelLevels.Pinned

open AlgebraicGeometry ModelTorsion RC.ModelInvariants
open scoped TensorProduct

private theorem normal_stalk_of_regular_retract {B S : Type*} [CommRing B] [CommRing S]
    [Algebra B S] [IsRegularRing S] (r : S →ₗ[B] B) (hr : r 1 = 1)
    (q : Ideal B) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let L := Localization.AtPrime q
  let T := L ⊗[B] S
  letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid S q.primeCompl
  let : IsLocalization M T :=
    (Algebra.isLocalization_iff_isPushout (A := L) q.primeCompl).mpr inferInstance
  let : IsRegularRing T :=
    IsRegularRing.of_ringEquiv (IsLocalization.algEquiv M (Localization M) T).toRingEquiv
  let s : T →ₗ[L] L := (Algebra.TensorProduct.rid B L L).toLinearMap.comp
    (r.baseChange L)
  have hs : s 1 = 1 := by
    change (Algebra.TensorProduct.rid B L L) ((1 : L) ⊗ₜ[B] r 1) = 1
    rw [hr, Algebra.TensorProduct.rid_tmul, one_smul]
  refine local_normal_of_split s hs (fun m hm => ?_) (fun m hm => ?_)
  · let : m.IsPrime := hm.isPrime
    infer_instance
  · let : m.IsPrime := hm.isPrime
    let : IsRegularRing (Localization.AtPrime m) := IsRegularRing.localization _
    let := IsRegularLocalRing.uniqueFactorizationMonoid (Localization.AtPrime m)
    exact UniqueFactorizationMonoid.instIsIntegrallyClosed

private theorem normal_degreeZeroInvariants {k S G : Type*} [Field k] [CommRing S]
    [Algebra k S] [IsRegularRing S] [Group G] [Fintype G] [MulSemiringAction G S]
    [SMulCommClass G k S] (gr : ℤ → Submodule k S) [GradedAlgebra gr]
    [PreservesGrading (G := G) gr] (hcard : IsUnit (Fintype.card G : k))
    (q : Ideal (degreeZero (fixedGrading gr G))) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let F := ↥(FixedPoints.subalgebra k S G)
  let B := ↥(degreeZero (fixedGrading gr G))
  let f : B →+* S := (algebraMap F S).comp (algebraMap B F)
  letI : Algebra B S := f.toAlgebra
  let : IsScalarTower B F S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let r := (degreeZeroProjection (fixedGrading gr G)).comp
    ((reynolds (S := S) G hcard).restrictScalars B)
  have hr : r 1 = 1 := by
    change degreeZeroProjection (fixedGrading gr G) (reynolds (S := S) G hcard (1 : S)) = 1
    rw [show reynolds (S := S) G hcard (1 : S) = (1 : F) from reynolds_fixed hcard (1 : F)]
    exact degreeZeroProjection_fixed _ (1 : B)
  exact normal_stalk_of_regular_retract r hr q

private theorem normal_stalk_of_ringEquiv {B C : Type*} [CommRing B] [CommRing C] (e : B ≃+* C)
    (q : Ideal C) [q.IsPrime]
    (h : ∀ (m : Ideal B) [m.IsPrime],
      IsDomain (Localization.AtPrime m) ∧ IsIntegrallyClosed (Localization.AtPrime m)) :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let m := q.comap e
  let : m.IsPrime := Ideal.comap_isPrime e q
  let E := IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime m) (Localization.AtPrime q)
    e (e.map_primeCompl_comap_eq q)
  let : IsDomain (Localization.AtPrime m) := (h m).1
  let : IsIntegrallyClosed (Localization.AtPrime m) := (h m).2
  exact ⟨E.isDomain_iff.mp ‹_›, IsIntegrallyClosed.of_equiv E⟩

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell)
    (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)

set_option maxHeartbeats 700000 in
set_option backward.isDefEq.respectTransparency false in
/-- Each local ring on a field fibre of the pinned quotient is a normal domain. -/
theorem levelQuotient_fibre_normal (k : Type*) [Field k] [Algebra (LocalIntegers ell) k]
    (q : Ideal (k ⊗[LocalIntegers ell] Y0LevelAlgebra h₅ htame h₂)) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let R := LocalIntegers ell
  let S := UniversalExactOrderAlgebra ell N h₅ htame
  letI := detectorLevelAction h₅ htame h₂
  letI := detectorLevelAction_comm h₅ htame h₂
  letI := detectorExactOrderGradedAlgebra h₅ htame h₂
  letI := detectorLevelAction_preserves h₅ htame h₂
  let : IsRegularRing (k ⊗[R] S) := detectorCover_field_regular h₅ htame k
  let gr := fun i => (detectorExactOrderGrading h₅ htame h₂ i).baseChange k
  let e := levelQuotientBaseChange h₅ htame h₂ k
  have hc : IsUnit (Fintype.card (ZMod N)ˣ : R) := by
    simpa only [Nat.card_eq_fintype_card] using (detector_units ell N h₅ htame).2.2
  have hck : IsUnit (Fintype.card (ZMod N)ˣ : k) := by
    have he : (algebraMap R k) (Fintype.card (ZMod N)ˣ : R) =
        (Fintype.card (ZMod N)ˣ : k) := map_natCast (algebraMap R k) _
    exact he ▸ hc.map (algebraMap R k)
  let F := degreeZero (fixedGrading gr (ZMod N)ˣ)
  let : CommRing ↥F := F.toCommRing
  apply normal_stalk_of_ringEquiv (B := ↥F) e.symm.toRingEquiv q
  intro m _
  exact normal_degreeZeroInvariants gr hck m

/-- The pinned coordinate algebra is smooth over the detector ring. -/
theorem levelQuotient_smooth :
    Algebra.Smooth (LocalIntegers ell) (Y0LevelAlgebra h₅ htame h₂) := by
  apply levelQuotient_smooth_of_geometric_normal h₅ htame h₂
  intro k _ _ _ q _
  exact levelQuotient_fibre_normal h₅ htame h₂ k q

/-- The pinned integral affine model has smooth structure map over the detector. -/
theorem Y0Level_smooth : Smooth (Y0Level h₅ htame h₂).hom := by
  change Smooth (Spec.map (CommRingCat.ofHom (S := ↥(Y0LevelAlgebra h₅ htame h₂))
    (algebraMap (LocalIntegers ell) (Y0LevelAlgebra h₅ htame h₂))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr (levelQuotient_smooth h₅ htame h₂)

#print axioms normal_stalk_of_regular_retract
#print axioms normal_degreeZeroInvariants
#print axioms normal_stalk_of_ringEquiv
#print axioms levelQuotient_fibre_normal
#print axioms levelQuotient_smooth
#print axioms Y0Level_smooth

end WeierstrassCurve.ModelLevels.Pinned
