import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelPoints
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.ShortSliceFinite

/-! # Finiteness of the pinned quotient over the j-line -/

namespace WeierstrassCurve.ModelLevels.Pinned

open ModelTorsion RC.ModelInvariants
open scoped TensorProduct

open private detectorShort_domain detectorLevel_isUnit from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels2.DetectorCyclicLevel
open private detectorCoverAlgebra detectorCoverTower from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0Level
open private homogeneousUnit_inv_mem degreeZero_not_in_span from
  ZInQKernel.Contrib.OneProof.RC.ModelInvariants.GradedPoints

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell)
  (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem detectorJ_mem :
    algebraMap (ShortBase (LocalIntegers ell)) (UniversalExactOrderAlgebra ell N h₅ htame)
      (shortFamily (LocalIntegers ell)).j ∈ detectorExactOrderGrading h₅ htame h₂ 0 := by
  obtain _ | _ | n := N
  · omega
  · omega
  let R := LocalIntegers ell
  let A := ShortBase R
  let S := UniversalExactOrderAlgebra ell (n + 2) h₅ htame
  let W := shortFamily R
  let hn := detectorLevel_isUnit h₅ htame
  let gr := detectorExactOrderGrading h₅ htame h₂
  letI := detectorCoverAlgebra h₅ htame
  letI := detectorCoverTower h₅ htame
  letI := detectorShort_domain h₅ htame
  letI : GradedAlgebra gr := detectorExactOrderGradedAlgebra h₅ htame h₂
  let : W.IsShortNF := shortFamily_IsShortNF
  let δ : Sˣ := shortExactOrderDiscriminantUnit (R := R) hn
  have hδ : (δ : S) ∈ gr 12 := shortExactOrderDiscriminantUnit_mem (R := R) hn
  have hδinv : (↑δ⁻¹ : S) ∈ gr (-12) := homogeneousUnit_inv_mem gr hδ
  have h4 : algebraMap A S W.a₄ ∈ gr 4 := shortExactOrderCoordinates_mem (R := R) hn 0
  have hc4 : algebraMap A S W.c₄ ∈ gr 4 := by
    have hm : (-48 : R) • (algebraMap A S W.a₄) ∈ gr 4 := (gr 4).smul_mem (-48 : R) h4
    let f := algebraMap A S
    have hc : f W.c₄ = (-48 : S) * f W.a₄ := by
      rw [W.c₄_of_isShortNF, f.map_mul, f.map_neg, map_ofNat f]
    change f W.c₄ ∈ gr 4
    rw [hc]
    rwa [Algebra.smul_def, (algebraMap R S).map_neg, map_ofNat (algebraMap R S)] at hm
  change algebraMap A S W.j ∈ gr 0
  rw [WeierstrassCurve.j, map_mul, map_pow]
  exact SetLike.mul_mem_graded hδinv (SetLike.pow_mem_graded 3 hc4)

/-- The actual short-family j-invariant in the pinned degree-zero ring. -/
noncomputable def Y0LevelJ : Y0LevelAlgebra h₅ htame h₂ := by
  letI := detectorLevelAction h₅ htame h₂
  letI := detectorLevelAction_comm h₅ htame h₂
  letI := detectorExactOrderGradedAlgebra h₅ htame h₂
  letI := detectorLevelAction_preserves h₅ htame h₂
  letI := detectorShort_domain h₅ htame
  let W := shortFamily (LocalIntegers ell)
  refine ⟨⟨algebraMap _ _ W.j, ?_⟩, detectorJ_mem h₅ htame h₂⟩
  intro a
  exact (levelUnitAut W (detectorLevel_isUnit h₅ htame) h₂ a).commutes W.j

/-- The polynomial coordinate on the j-line maps to the actual j-invariant. -/
noncomputable def Y0LevelJMap :
    Polynomial (LocalIntegers ell) →ₐ[LocalIntegers ell] Y0LevelAlgebra h₅ htame h₂ :=
  Polynomial.aeval (Y0LevelJ h₅ htame h₂)

private theorem finite_of_discriminant_slice {R S B : Type*} {A : Type v} [CommRing R] [CommRing A]
    [CommRing S] [CommRing B] [Algebra R A] [Algebra R S] [Algebra A S]
    [IsScalarTower R A S] [Algebra R B] [Module.Finite A S] [IsNoetherianRing R]
    (W : WeierstrassCurve A) [W.IsElliptic]
    (gr : ℤ → Submodule R S) [GradedAlgebra gr] (δ : Sˣ)
    (hD : algebraMap A S W.Δ = (δ : S)) (hδ : (δ : S) ∈ gr 12)
    (inc : B →ₐ[R] S) (hinj : Function.Injective inc) (hgr : ∀ b, inc b ∈ gr 0)
    (j : B) (hj : inc j = algebraMap A S W.j)
    (hA : ∀ (T : Type v) [CommRing T] [Algebra R T] (a : A →ₐ[R] T),
      Function.Surjective a → a W.Δ = 1 →
      letI : Algebra (Polynomial R) T := (Polynomial.aeval (a W.j)).toRingHom.toAlgebra
      Module.Finite (Polynomial R) T) :
    letI : Algebra (Polynomial R) B := (Polynomial.aeval j).toRingHom.toAlgebra
    Module.Finite (Polynomial R) B := by
  let I : Ideal A := Ideal.span {W.Δ - 1}
  let J : Ideal S := I.map (algebraMap A S)
  let A' := A ⧸ I
  let T := S ⧸ J
  let q := Ideal.Quotient.mkₐ R J
  let a := Ideal.Quotient.mkₐ R I
  let P := Polynomial R
  let jA : P →ₐ[R] A' := Polynomial.aeval (a W.j)
  let jB : P →ₐ[R] B := Polynomial.aeval j
  let i : B →ₐ[R] T := q.comp inc
  letI : Algebra P A' := jA.toRingHom.toAlgebra
  letI : Algebra P T := ((algebraMap A' T).comp jA.toRingHom).toAlgebra
  let : IsScalarTower R A' T := IsScalarTower.of_algebraMap_eq fun r => by
    change q (algebraMap R S r) = q (algebraMap A S (algebraMap R A r))
    rw [IsScalarTower.algebraMap_apply R A S]
  let : IsScalarTower P A' T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra P B := jB.toRingHom.toAlgebra
  letI : Algebra B T := i.toRingHom.toAlgebra
  have hP : i.comp jB = (IsScalarTower.toAlgHom R A' T).comp jA := by
    apply Polynomial.algHom_ext
    change (q.comp inc) (Polynomial.aeval j Polynomial.X) =
      algebraMap A' T (Polynomial.aeval (a W.j) Polynomial.X)
    rw [Polynomial.aeval_X, Polynomial.aeval_X]
    change q (inc j) = _
    rw [hj]
    rfl
  let : IsScalarTower P B T := IsScalarTower.of_algebraMap_eq fun p => (AlgHom.congr_fun hP p).symm
  have ha : a W.Δ = 1 := by
    apply sub_eq_zero.mp
    rw [← map_one a, ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  let : Module.Finite P A' := hA A' a (Ideal.Quotient.mkₐ_surjective R I) ha
  let : Module.Finite A' T :=
    Module.Finite.equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I).symm.toLinearEquiv
  let : Module.Finite P T := Module.Finite.trans A' T
  have hJ : J = Ideal.span {(δ : S) - 1} := by
    change I.map (algebraMap A S) = _
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one, hD]
  have hi : Function.Injective i := (injective_iff_map_eq_zero i).mpr fun x hx => by
    have hxJ : inc x ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hx
    rw [hJ] at hxJ
    apply hinj
    rw [map_zero]
    exact degreeZero_not_in_span gr (by decide : 0 < (12 : ℤ)) hδ (hgr x) hxJ
  exact Module.Finite.of_injective (IsScalarTower.toAlgHom P B T).toLinearMap hi

set_option maxHeartbeats 600000 in
set_option backward.isDefEq.respectTransparency false in
/-- The pinned quotient is finite over the j-line. The weight-zero ring
embeds in the discriminant-one slice, which is finite over the normalized
short slice by base change of the finite exact-order cover. -/
theorem Y0LevelJMap_finite :
    letI : Algebra (Polynomial (LocalIntegers ell)) (Y0LevelAlgebra h₅ htame h₂) :=
      (Y0LevelJMap h₅ htame h₂).toRingHom.toAlgebra
    Module.Finite (Polynomial (LocalIntegers ell)) (Y0LevelAlgebra h₅ htame h₂) := by
  obtain _ | _ | n := N
  · omega
  · omega
  let R := LocalIntegers ell
  let A := ShortBase R
  let S := UniversalExactOrderAlgebra ell (n + 2) h₅ htame
  let W := shortFamily R
  let hn := detectorLevel_isUnit h₅ htame
  let gr := detectorExactOrderGrading h₅ htame h₂
  letI := detectorCoverAlgebra h₅ htame
  letI := detectorCoverTower h₅ htame
  letI := detectorShort_domain h₅ htame
  letI : GradedAlgebra gr := detectorExactOrderGradedAlgebra h₅ htame h₂
  let : Module.Finite A S := (universalExactOrder_finite_etale ell (n + 2) h₅ htame).1
  let δ : Sˣ := shortExactOrderDiscriminantUnit (R := R) hn
  let e := Y0LevelInclusion h₅ htame h₂
  let j := Y0LevelJ h₅ htame h₂
  apply finite_of_discriminant_slice W gr δ rfl (shortExactOrderDiscriminantUnit_mem (R := R) hn)
    e (Subtype.val_injective.comp Subtype.val_injective) (fun x => x.property) j rfl
  intro T _ _ a ha hD
  exact shortDiscriminantSlice_finite (detector_units ell (n + 2) h₅ htame).1 a ha hD

/-- The pinned coordinate algebra is of finite type over the detector ring. -/
theorem levelQuotient_finiteType :
    Algebra.FiniteType (LocalIntegers ell) (Y0LevelAlgebra h₅ htame h₂) := by
  let R := LocalIntegers ell
  let P := Polynomial R
  let B := Y0LevelAlgebra h₅ htame h₂
  let jB : P →ₐ[R] B := Y0LevelJMap h₅ htame h₂
  letI : Algebra P B := jB.toRingHom.toAlgebra
  letI : IsScalarTower R P B := IsScalarTower.of_algebraMap_eq fun r => (jB.commutes r).symm
  letI : Module.Finite P B := Y0LevelJMap_finite h₅ htame h₂
  exact (inferInstance : Algebra.FiniteType R P).trans (inferInstance : Algebra.FiniteType P B)

/-- The pinned coordinate algebra is finitely presented over the detector ring. -/
theorem levelQuotient_finitePresentation :
    Algebra.FinitePresentation (LocalIntegers ell) (Y0LevelAlgebra h₅ htame h₂) :=
  (Algebra.FinitePresentation.of_finiteType (R := LocalIntegers ell)
    (A := ↥(Y0LevelAlgebra h₅ htame h₂))).mp (levelQuotient_finiteType h₅ htame h₂)

#print axioms detectorJ_mem
#print axioms Y0LevelJ
#print axioms Y0LevelJMap
#print axioms finite_of_discriminant_slice
#print axioms Y0LevelJMap_finite
#print axioms levelQuotient_finiteType
#print axioms levelQuotient_finitePresentation

end WeierstrassCurve.ModelLevels.Pinned
