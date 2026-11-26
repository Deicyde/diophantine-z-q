import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelFinite

/-! # The pinned rational short-level quotient -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric

open AlgebraicGeometry CategoryTheory ModelTorsion RC.ModelInvariants

open private shortDiscriminant_ne_zero from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels2.DetectorCyclicLevel

open private exactOrderPointOfGenerator_coefficients from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels3.ExactOrderScaling

open private finite_of_discriminant_slice from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelFinite

private instance : IsDomain (ShortBase ℚ) :=
  Localization.Away.isDomain (shortDiscriminant_ne_zero ℚ (by norm_num))

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

private theorem rationalLevel_isUnit : IsUnit (N : ShortBase ℚ) := by
  simpa only [map_natCast] using
    (isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne N) : (N : ℚ) ≠ 0)).map
      (algebraMap ℚ (ShortBase ℚ))

/-- The exact-order cover over the universal short curve over the rationals. -/
noncomputable abbrev rationalCover (N : ℕ) [NeZero N] :=
  ExactOrderAlgebra (shortFamily ℚ) (rationalLevel_isUnit (N := N))

noncomputable instance : Algebra ℚ (rationalCover N) :=
  ((algebraMap (ShortBase ℚ) (rationalCover N)).comp (algebraMap ℚ (ShortBase ℚ))).toAlgebra

instance : IsScalarTower ℚ (ShortBase ℚ) (rationalCover N) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The grading given by weights `4, 6, 2, 3, -12` on the two coefficients, the
two coordinates of the marked generator, and the inverse discriminant. -/
noncomputable def rationalGrading : ℤ → Submodule ℚ (rationalCover N) := by
  obtain _ | _ | n := N
  · omega
  · omega
  · exact shortExactOrderGrading (R := ℚ) (n := n) rationalLevel_isUnit

@[instance_reducible] noncomputable def rationalGradedAlgebra :
    GradedAlgebra (rationalGrading h₂) := by
  obtain _ | _ | n := N
  · omega
  · omega
  · exact shortExactOrderGradedAlgebra (R := ℚ) (n := n) rationalLevel_isUnit

/-- Geometric change of generator on the rational exact-order cover. -/
@[instance_reducible] noncomputable def rationalAction :
    MulSemiringAction (ZMod N)ˣ (rationalCover N) :=
  levelSemiringAction (shortFamily ℚ) rationalLevel_isUnit h₂

theorem rationalAction_comm :
    letI := rationalAction h₂
    SMulCommClass (ZMod N)ˣ ℚ (rationalCover N) := by
  letI := rationalAction h₂
  refine ⟨fun g r x => ?_⟩
  let e := (levelUnitAut (shortFamily ℚ) rationalLevel_isUnit h₂ g).restrictScalars ℚ
  exact e.toAlgHom.toLinearMap.map_smul r x

theorem rationalAction_preserves :
    letI := rationalAction h₂
    letI := rationalAction_comm h₂
    letI := rationalGradedAlgebra h₂
    PreservesGrading (G := (ZMod N)ˣ) (rationalGrading h₂) := by
  obtain _ | _ | n := N
  · omega
  · omega
  · letI := rationalAction h₂
    letI := rationalAction_comm h₂
    letI := rationalGradedAlgebra h₂
    exact ⟨fun a i x hx => shortLevelUnitAut_mem (R := ℚ) rationalLevel_isUnit a hx⟩

/-- The detector-independent coordinate algebra `(S_N^H)_0`, formed over
`ℚ[a₄,a₆,Δ⁻¹]` with the geometric change of generator and the short weights. -/
noncomputable abbrev Y0RationalAlgebra :=
  letI := rationalAction h₂
  letI := rationalAction_comm h₂
  letI := rationalGradedAlgebra h₂
  letI := rationalAction_preserves h₂
  degreeZero (fixedGrading (rationalGrading h₂) (ZMod N)ˣ)

/-- The affine rational moduli quotient with its structure map over `ℚ`. -/
noncomputable def Y0Rational : Over (Spec (CommRingCat.of ℚ)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ (Y0RationalAlgebra h₂))))

/-- The inclusion of the rational degree-zero invariants in the exact-order cover. -/
noncomputable def Y0RationalInclusion : Y0RationalAlgebra h₂ →ₐ[ℚ] rationalCover N := by
  letI := rationalAction h₂
  letI := rationalAction_comm h₂
  letI := rationalGradedAlgebra h₂
  letI := rationalAction_preserves h₂
  exact degreeZeroInvariantsInclusion (G := (ZMod N)ˣ) (rationalGrading h₂)

set_option backward.isDefEq.respectTransparency false in
private theorem rationalJ_mem :
    algebraMap (ShortBase ℚ) (rationalCover N) (shortFamily ℚ).j ∈ rationalGrading h₂ 0 := by
  obtain _ | _ | n := N
  · omega
  · omega
  let hn := rationalLevel_isUnit (N := n + 2)
  apply shortExactOrderGrading_mem_of_field_scaling
  intro k _ _ _ u f
  let c := (shortExactOrderPoints hn f).1
  let W := (shortFamily ℚ).map c.toRingHom
  letI : W.IsShortNF := ⟨by simp [W, shortFamily, shortEquation],
    by simp [W, shortFamily, shortEquation], by simp [W, shortFamily, shortEquation]⟩
  let V := shortScaling u • W
  letI : V.IsShortNF := (shortScaling_coefficients W u).1
  change scaleShortExactOrderPoint hn u f (algebraMap _ _ (shortFamily ℚ).j) =
    (u : k) ^ (0 : ℤ) * c (shortFamily ℚ).j
  rw [zpow_zero, one_mul]
  unfold scaleShortExactOrderPoint
  rw [exactOrderPointOfGenerator_coefficients]
  have hV : shortCoefficientPoint (R := ℚ) V (shortFamily ℚ).j = V.j := by
    refine (WeierstrassCurve.map_j (shortFamily ℚ)
      (shortCoefficientPoint (R := ℚ) V).toRingHom).symm.trans ?_
    simpa only [WeierstrassCurve.j_eq] using congrArg
      (fun t : WeierstrassCurve k => t.Δ⁻¹ * t.c₄ ^ 3)
      (shortFamily_map_coefficientPoint (R := ℚ) V)
  rw [hV, variableChange_j]
  exact WeierstrassCurve.map_j _ _

/-- The invariant of the source elliptic equation in the pinned rational ring. -/
noncomputable def Y0RationalJ : Y0RationalAlgebra h₂ := by
  letI := rationalAction h₂
  letI := rationalAction_comm h₂
  letI := rationalGradedAlgebra h₂
  letI := rationalAction_preserves h₂
  let W := shortFamily ℚ
  refine ⟨⟨algebraMap _ _ W.j, ?_⟩, rationalJ_mem h₂⟩
  intro a
  exact (levelUnitAut W rationalLevel_isUnit h₂ a).commutes W.j

/-- The morphism to the affine j-line on coordinate rings. -/
noncomputable def Y0RationalJMap : Polynomial ℚ →ₐ[ℚ] Y0RationalAlgebra h₂ :=
  Polynomial.aeval (Y0RationalJ h₂)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
/-- The rational moduli quotient is finite over the actual affine j-line. -/
theorem Y0RationalJMap_finite :
    letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
    Module.Finite (Polynomial ℚ) (Y0RationalAlgebra h₂) := by
  obtain _ | _ | n := N
  · omega
  · omega
  let W := shortFamily ℚ
  let hn := rationalLevel_isUnit (N := n + 2)
  letI : GradedAlgebra (rationalGrading h₂) := rationalGradedAlgebra h₂
  let : Module.Finite (ShortBase ℚ) (rationalCover (n + 2)) := (exactOrderAlgebra_finite_etale W hn).1
  exact finite_of_discriminant_slice W (rationalGrading h₂)
    (shortExactOrderDiscriminantUnit (R := ℚ) hn) rfl
    (shortExactOrderDiscriminantUnit_mem (R := ℚ) hn) (Y0RationalInclusion h₂)
    (Subtype.val_injective.comp Subtype.val_injective) (fun x => x.property)
    (Y0RationalJ h₂) rfl (fun _ _ _ a ha hD => shortDiscriminantSlice_finite
      (isUnit_iff_ne_zero.mpr (by norm_num : (6 : ℚ) ≠ 0)) a ha hD)

#print axioms rationalLevel_isUnit
#print axioms rationalCover
#print axioms rationalGrading
#print axioms rationalGradedAlgebra
#print axioms rationalAction
#print axioms rationalAction_comm
#print axioms rationalAction_preserves
#print axioms Y0RationalAlgebra
#print axioms Y0Rational
#print axioms Y0RationalInclusion
#print axioms rationalJ_mem
#print axioms Y0RationalJ
#print axioms Y0RationalJMap
#print axioms Y0RationalJMap_finite

end WeierstrassCurve.ModelLevels.ModelGeneric
