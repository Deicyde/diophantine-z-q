import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0LevelPoints
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric7.PairMap

/-! **The computation lemma and the naturality of `Pinned.Y0LevelPoints`** (rc-model-generic7,
item 3, pieces (b) and the naturality).

`Pinned.Y0LevelPoints` (`RC/ModelLevels3/Y0LevelPoints.lean`) is built with `Equiv.ofBijective`
inside a tactic block, from a chosen lift of each point to the universal exact-order cover, and
has no computation lemma. This file proves it:

* `Y0LevelPoints_comp_inclusion`: for every cover point `f` (over every algebraically closed `k`
  with `Algebra (LocalIntegers ell) k`, in any characteristic),
  `Y0LevelPoints (f ∘ Y0LevelInclusion) = [shortCoverPair f]`, at level `n + 2` (the split that
  `Y0LevelPoints` itself makes).
* `exists_comp_inclusion`: every `k`-point of the pinned level algebra is `f ∘ Y0LevelInclusion`
  for a cover point `f` (`degreeZeroInvariants_restrict_surjective`).
* `Y0LevelPoints_comp`: naturality along every `LocalIntegers ell`-algebra map `σ : k₁ → k₂` of
  algebraically closed fields, `Y0LevelPoints (σ ∘ x) = pairClassesMap σ (Y0LevelPoints x)`, and
  `Y0LevelPoints_algEquiv` for an algebra isomorphism.

The proof of the computation lemma repeats the internal step `equivalent` of `Y0LevelPoints`
(the lead's second named copy exception), which needs the four private declarations that
`Y0LevelPoints.lean` opens; they are reached here with the same `open private` lines. -/

set_option autoImplicit false

noncomputable section

namespace ZInQ.Manuscript.RC.ModelGeneric7

open WeierstrassCurve WeierstrassCurve.ModelLevels WeierstrassCurve.ModelTorsion
  WeierstrassCurve.ModelLevels.Pinned RC.ModelInvariants

open private detectorShort_domain detectorLevel_isUnit from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels2.DetectorCyclicLevel
open private detectorCoverAlgebra detectorCoverTower from
  ZInQKernel.Contrib.OneProof.RC.ModelLevels3.Y0Level

variable {ell : ℕ} [Fact ell.Prime]

/-- The level `n + 2` is a unit on the short locus over `LocalIntegers ell` (a public restatement
of the proof carried by `UniversalExactOrderAlgebra`). -/
theorem coverLevel_isUnit {n : ℕ} [NeZero (n + 2)] (h₅ : 5 ≤ ell)
    (htame : ¬ ell ∣ (n + 2) * (n + 2).totient) :
    IsUnit (((n + 2 : ℕ) : ShortBase (LocalIntegers ell))) := by
  exact_mod_cast (detector_units ell (n + 2) h₅ htame).2.1.map
    (algebraMap (LocalIntegers ell) (ShortBase (LocalIntegers ell)))

variable {k : Type*} [Field k] [Algebra (LocalIntegers ell) k] [DecidableEq k] [IsAlgClosed k]

/-- The pair read on a point `f` of the universal exact-order cover: `shortCoverPair f`, with the
cover's global `LocalIntegers ell`-algebra and scalar-tower instances. -/
noncomputable def coverPair {n : ℕ} [NeZero (n + 2)] (h₅ : 5 ≤ ell)
    (htame : ¬ ell ∣ (n + 2) * (n + 2).totient)
    (f : UniversalExactOrderAlgebra ell (n + 2) h₅ htame →ₐ[LocalIntegers ell] k) :
    EnhancedCurve k (n + 2) :=
  letI : Algebra (LocalIntegers ell)
      (ExactOrderAlgebra (shortFamily (LocalIntegers ell)) (coverLevel_isUnit h₅ htame)) :=
    inferInstanceAs (Algebra (LocalIntegers ell) (UniversalExactOrderAlgebra ell (n + 2) h₅ htame))
  letI : IsScalarTower (LocalIntegers ell) (ShortBase (LocalIntegers ell))
      (ExactOrderAlgebra (shortFamily (LocalIntegers ell)) (coverLevel_isUnit h₅ htame)) :=
    inferInstanceAs (IsScalarTower (LocalIntegers ell) (ShortBase (LocalIntegers ell))
      (UniversalExactOrderAlgebra ell (n + 2) h₅ htame))
  shortCoverPair (coverLevel_isUnit h₅ htame) f

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **The computation lemma of `Pinned.Y0LevelPoints`** (3b (i)): at a cover point `f`, the
reading is the class of the pair `shortCoverPair f` read on the cover. The preamble repeats the
`let` lines of `Y0LevelPoints` (`RC/ModelLevels3/Y0LevelPoints.lean:42-63`); `equivalent` is
the copied internal step. -/
theorem Y0LevelPoints_comp_inclusion {n : ℕ} [NeZero (n + 2)] (h₅ : 5 ≤ ell)
    (htame : ¬ ell ∣ (n + 2) * (n + 2).totient) (h₂ : 2 ≤ n + 2)
    (f : UniversalExactOrderAlgebra ell (n + 2) h₅ htame →ₐ[LocalIntegers ell] k) :
    Y0LevelPoints h₅ htame h₂ (f.comp (Y0LevelInclusion h₅ htame h₂)) =
      Quot.mk _ (coverPair h₅ htame f) := by
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
  -- Copied from ZInQKernel/Contrib/OneProof/RC/ModelLevels3/Y0LevelPoints.lean:64-90
  -- (the internal step `equivalent` of `Pinned.Y0LevelPoints`), base SHA
  -- aba99b7b2e3eea8804ebeffd1834ba5f31fa9c7e; statement and proof unchanged.
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
  -- End of the copied block.
  have key : read (hlift (restrict f)).choose = read f :=
    (equivalent _ _).1 (hlift (restrict f)).choose_spec
  exact key

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Every `k`-point of the pinned level algebra comes from a point of the universal exact-order
cover (`degreeZeroInvariants_restrict_surjective`). -/
theorem exists_comp_inclusion {n : ℕ} [NeZero (n + 2)] (h₅ : 5 ≤ ell)
    (htame : ¬ ell ∣ (n + 2) * (n + 2).totient) (h₂ : 2 ≤ n + 2)
    (x : Pinned.Y0LevelAlgebra h₅ htame h₂ →ₐ[LocalIntegers ell] k) :
    ∃ f : UniversalExactOrderAlgebra ell (n + 2) h₅ htame →ₐ[LocalIntegers ell] k,
      f.comp (Y0LevelInclusion h₅ htame h₂) = x := by
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
  exact degreeZeroInvariants_restrict_surjective (G := (ZMod (n + 2))ˣ) (k := k) grading
    (by decide) hδ x

variable {N : ℕ} [NeZero N]
  {k₁ k₂ : Type*} [Field k₁] [Field k₂] [Algebra (LocalIntegers ell) k₁]
  [Algebra (LocalIntegers ell) k₂] [DecidableEq k₁] [DecidableEq k₂] [IsAlgClosed k₁]
  [IsAlgClosed k₂]

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- **Naturality of `Pinned.Y0LevelPoints`** along every `LocalIntegers ell`-algebra map of
algebraically closed fields, in any characteristic:
`Y0LevelPoints (σ ∘ x) = pairClassesMap σ (Y0LevelPoints x)`. From the computation lemma at a
cover lift of `x` and `shortCoverPair_class_comp`. -/
theorem Y0LevelPoints_comp (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)
    (σ : k₁ →ₐ[LocalIntegers ell] k₂)
    (x : Pinned.Y0LevelAlgebra h₅ htame h₂ →ₐ[LocalIntegers ell] k₁) :
    Y0LevelPoints h₅ htame h₂ (σ.comp x) =
      pairClassesMap (σ : k₁ →+* k₂) N (Y0LevelPoints h₅ htame h₂ x) := by
  obtain _ | _ | n := N
  · omega
  · omega
  obtain ⟨f, rfl⟩ := exists_comp_inclusion h₅ htame h₂ x
  rw [← AlgHom.comp_assoc, Y0LevelPoints_comp_inclusion, Y0LevelPoints_comp_inclusion]
  letI : Algebra (LocalIntegers ell)
      (ExactOrderAlgebra (shortFamily (LocalIntegers ell)) (coverLevel_isUnit h₅ htame)) :=
    inferInstanceAs (Algebra (LocalIntegers ell) (UniversalExactOrderAlgebra ell (n + 2) h₅ htame))
  letI : IsScalarTower (LocalIntegers ell) (ShortBase (LocalIntegers ell))
      (ExactOrderAlgebra (shortFamily (LocalIntegers ell)) (coverLevel_isUnit h₅ htame)) :=
    inferInstanceAs (IsScalarTower (LocalIntegers ell) (ShortBase (LocalIntegers ell))
      (UniversalExactOrderAlgebra ell (n + 2) h₅ htame))
  exact shortCoverPair_class_comp (coverLevel_isUnit h₅ htame) σ f

/-- `Y0LevelPoints_comp` along an algebra isomorphism `σ : k₁ ≃ₐ[LocalIntegers ell] k₂` (the
form SP2's `point_frob` uses at the Frobenius automorphism of the residue field). -/
theorem Y0LevelPoints_algEquiv (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)
    (σ : k₁ ≃ₐ[LocalIntegers ell] k₂)
    (x : Pinned.Y0LevelAlgebra h₅ htame h₂ →ₐ[LocalIntegers ell] k₁) :
    Y0LevelPoints h₅ htame h₂ (σ.toAlgHom.comp x) =
      pairClassesMap σ.toRingEquiv.toRingHom N (Y0LevelPoints h₅ htame h₂ x) :=
  Y0LevelPoints_comp h₅ htame h₂ σ.toAlgHom x

end ZInQ.Manuscript.RC.ModelGeneric7

#print axioms ZInQ.Manuscript.RC.ModelGeneric7.coverLevel_isUnit
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.Y0LevelPoints_comp_inclusion
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.exists_comp_inclusion
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.Y0LevelPoints_comp
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.Y0LevelPoints_algEquiv
