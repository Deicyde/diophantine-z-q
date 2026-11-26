import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0Level
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.QuotientPointLifts
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.ExactOrderIdempotents
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.CoverPairs

/-! # Points of the pinned short-level quotient -/

namespace WeierstrassCurve.ModelLevels.Pinned

open ModelTorsion RC.ModelInvariants

open private detectorShort_domain detectorLevel_isUnit from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels2.DetectorCyclicLevel
open private detectorCoverAlgebra detectorCoverTower from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0Level

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N] (h₅ : 5 ≤ ell)
  (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)

noncomputable def Y0LevelInclusion :
    Y0LevelAlgebra h₅ htame h₂ →ₐ[LocalIntegers ell] UniversalExactOrderAlgebra ell N h₅ htame := by
  letI := detectorLevelAction h₅ htame h₂
  letI := detectorLevelAction_comm h₅ htame h₂
  letI := detectorExactOrderGradedAlgebra h₅ htame h₂
  letI := detectorLevelAction_preserves h₅ htame h₂
  exact degreeZeroInvariantsInclusion (G := (ZMod N)ˣ) (detectorExactOrderGrading h₅ htame h₂)

variable {k : Type*} [Field k] [Algebra (LocalIntegers ell) k] [DecidableEq k] [IsAlgClosed k]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The geometric points of the pinned quotient are isomorphism classes
of elliptic curves with a cyclic subgroup of order `N`. The field carries
only a map from the local integers, so the algebraic closure of the
detector residue field is included. -/
noncomputable def Y0LevelPoints :
    (Y0LevelAlgebra h₅ htame h₂ →ₐ[LocalIntegers ell] k) ≃ PairClasses k N := by
  obtain _ | _ | n := N
  · omega
  · omega
  let R := LocalIntegers ell
  let hn := detectorLevel_isUnit h₅ htame
  let S := UniversalExactOrderAlgebra ell (n + 2) h₅ htame
  let grading := detectorExactOrderGrading h₅ htame h₂
  letI := detectorCoverAlgebra h₅ htame
  letI := detectorCoverTower h₅ htame
  letI := detectorShort_domain h₅ htame
  letI := detectorLevelAction h₅ htame h₂
  letI := detectorLevelAction_comm h₅ htame h₂
  letI := detectorExactOrderGradedAlgebra h₅ htame h₂
  letI := detectorLevelAction_preserves h₅ htame h₂
  let δ : Sˣ := shortExactOrderDiscriminantUnit (R := R) hn
  have hδ : (δ : S) ∈ grading 12 := shortExactOrderDiscriminantUnit_mem (R := R) hn
  let restrict (f : S →ₐ[R] k) := f.comp (Y0LevelInclusion h₅ htame h₂)
  have hlift : Function.Surjective restrict :=
    degreeZeroInvariants_restrict_surjective (G := (ZMod (n + 2))ˣ) grading (by decide) hδ
  let read (f : S →ₐ[R] k) : PairClasses k (n + 2) := Quot.mk _ (shortCoverPair hn f)
  have h6 : IsUnit (6 : k) := by
    simpa only [map_ofNat] using ((detector_units ell (n + 2) h₅ htame).1.map (algebraMap R k))
  have hk₂ : (2 : k) ≠ 0 := (isUnit_of_dvd_unit (show (2 : k) ∣ 6 from ⟨3, by norm_num⟩) h6).ne_zero
  have hk₃ : (3 : k) ≠ 0 := (isUnit_of_dvd_unit (show (3 : k) ∣ 6 from ⟨2, by norm_num⟩) h6).ne_zero
  have hcard : IsUnit (Fintype.card (ZMod (n + 2))ˣ : R) := by
    simpa only [Nat.card_eq_fintype_card] using (detector_units ell (n + 2) h₅ htame).2.2
  have equivalent (f g : S →ₐ[R] k) : restrict f = restrict g ↔ read f = read g := by
    change _ ↔ (Quot.mk _ (shortCoverPair hn f) : PairClasses k (n + 2)) =
      Quot.mk _ (shortCoverPair hn g)
    rw [shortCoverPairClass_eq_iff hn hk₂ hk₃]
    have horbit := degreeZeroInvariants_restrict_eq_iff grading (by decide) hδ hcard f g
    change restrict f = restrict g ↔ _ at horbit
    rw [horbit]
    constructor
    · rintro ⟨a, u, hu⟩
      refine ⟨a⁻¹, u, ?_⟩
      have hact : a • f = f.comp (shortLevelUnitAut hn a⁻¹).toAlgHom := rfl
      rw [hact] at hu
      apply AlgHom.ext
      intro x
      refine DirectSum.Decomposition.inductionOn (ℳ := grading) ?_ ?_ ?_ x
      · simp
      · intro i y
        rw [hu i y y.property,
          scaleShortExactOrderPoint_homogeneous hn u _ y.property, Units.val_zpow_eq_zpow_val]
      · intro x y hx hy
        rw [map_add, map_add, hx, hy]
    · rintro ⟨a, u, ha⟩
      refine ⟨a⁻¹, u, fun i x hx => ?_⟩
      have hact : a⁻¹ • f = f.comp (shortLevelUnitAut hn a).toAlgHom := by
        change f.comp (shortLevelUnitAut hn (a⁻¹)⁻¹).toAlgHom = _
        rw [inv_inv]
      rw [ha, hact, scaleShortExactOrderPoint_homogeneous hn u _ hx, Units.val_zpow_eq_zpow_val]
  let value (x : Y0LevelAlgebra h₅ htame h₂ →ₐ[R] k) := read (hlift x).choose
  have value_restrict (f : S →ₐ[R] k) : value (restrict f) = read f :=
    (equivalent _ _).1 (hlift (restrict f)).choose_spec
  apply Equiv.ofBijective value
  constructor
  · intro x y hxy
    obtain ⟨f, rfl⟩ := hlift x
    obtain ⟨g, rfl⟩ := hlift y
    rw [value_restrict, value_restrict] at hxy
    exact (equivalent _ _).2 hxy
  · intro x
    obtain ⟨f, hf⟩ := shortCoverPairClass_surjective hn hk₂ hk₃ x
    exact ⟨restrict f, (value_restrict f).trans hf⟩

#print axioms Y0LevelInclusion
#print axioms Y0LevelPoints

end WeierstrassCurve.ModelLevels.Pinned
