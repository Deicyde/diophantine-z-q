/-
H5 Step2 / I0: affine complements exclude complete stabilizer cosets.
Copyright (c) 2026 H5 contributors. Apache-2.0.
SOURCE ONLY / UNCOMPILED. Native/kernel/currentABI/Std3 remains unproduced.

This is the RETAINED I0 stabilizer-finiteness piece, NOT C3's delegated
I2 support→IDEAL multiplicity proof. For an affine complement U containing
the actual identity, its setwise rational stabilizer is closed: on the
ACTUAL product D_red×A the projection is universally open, so the image of
the open failure locus is open. Rational closed-point density identifies
that image with failure of forward stability. Intersect with the inverse
parameter to obtain the true setwise stabilizer, not a false one-slice
line-bundle openness assertion.

If this closed subgroup has infinitely many points, reuse C3's EXACT native
E3 Source term in I1Status d292 (generic InfiniteClosedSubgroupContainsIntegral)
to obtain a proper integral nonfinite Y with mon-hom closed immersion j.
Every point of jY lies in U by setwise stability and identity∈U. Jacobson
closed-point density makes ALL of jY lie in U. Its actual lift to affine U
is a closed immersion, so Y is affine+proper, hence finite: contradiction.
Thus even the support stabilizer is finite; IDEAL H(D) is a SUBSET.

C3's E3/ConstructorParts and C5's native subset_of_closedPoint_subset are
SINGLE uncompiled Source suppliers, not copied proofs, new Facts or models.
D_red is used ONLY as the source of the support test; the ORIGINAL D ideal,
line and multiplicities are not changed or replaced. No Stacks imports,
CharZero/dimension/perfectness restriction or native/power/predicate alias.
-/
import NativeTranslationAction
import ZInQKernel.Contrib.CloudR2NOS.Step1.I1Status
import ZInQKernel.Contrib.CloudR2NOS.Step1.ConstructorParts
import GM3ClosedOpsOfPoints
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory TopologicalSpace
open scoped CategoryTheory.MonObj

namespace H5OriginalDVR.Lane2.NativeAffineComplementStabilizer

def pt {K : Type u} [Field K]
    (A : Grp (Over (Spec (CommRingCat.of K))))
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) : A.X.left :=
  x.left (IsLocalRing.closedPoint K)

/-- Forward rational support stability. This is a predicate of a GIVEN x,
not a claim that every translation preserves the support. -/
def Forward {K : Type u} [Field K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) (D : A.X.left.IdealSheafData)
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) : Prop :=
  ∀ d : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X,
    pt A d ∈ D.support → pt A (d * x) ∈ D.support

/-- The TRUE setwise rational stabilizer, retaining BOTH directions. -/
def supportPointStabilizer {K : Type u} [Field K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) (D : A.X.left.IdealSheafData) :
    Set (𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :=
  {x | ∀ d : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X,
    pt A d ∈ D.support ↔ pt A (d * x) ∈ D.support}

private theorem stabilizer_iff_forward_inverse {K : Type u} [Field K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) (D : A.X.left.IdealSheafData)
    (x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) :
    x ∈ supportPointStabilizer A D ↔ Forward A D x ∧ Forward A D x⁻¹ := by
  constructor
  · intro h
    refine ⟨fun d hd => (h d).mp hd, ?_⟩
    intro d hd
    apply (h (d * x⁻¹)).mpr
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hd
  · rintro ⟨hf, hi⟩ d
    refine ⟨hf d, fun hd => ?_⟩
    simpa only [mul_assoc, mul_inv_cancel, mul_one] using hi (d * x) hd

/-- Closed FORWARD stability locus from the OPEN failure image under the
actual D_red×A projection. This is not cube/line-seesaw openness. -/
theorem exists_closed_forward_locus
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData) :
    ∃ Z : Set A.X.left, IsClosed Z ∧
      ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X,
        Forward A D x ↔ pt A x ∈ Z := by
  classical
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  let I := Scheme.IdealSheafData.vanishingIdeal D.support
  let R : Over (Spec (CommRingCat.of K)) := Over.mk (I.subschemeι ≫ A.X.hom)
  let j : R ⟶ A.X := Over.homMk I.subschemeι rfl
  let P := R ⊗ A.X
  let q : P ⟶ A.X := snd R A.X
  let m : P ⟶ A.X := (fst R A.X ≫ j) * q
  haveI : LocallyOfFiniteType R.hom := inferInstance
  haveI : LocallyOfFiniteType P.hom := inferInstance
  haveI : JacobsonSpace P.left := LocallyOfFiniteType.jacobsonSpace P.hom
  haveI : UniversallyOpen R.hom := inferInstance
  haveI : UniversallyOpen q.left :=
    inferInstanceAs (UniversallyOpen (pullback.snd R.hom A.X.hom))
  let W : P.left.Opens := m.left ⁻¹ᵁ
    ⟨(D.support : Set A.X.left)ᶜ, D.support.isClosed.isOpen_compl⟩
  let F : Set A.X.left := q.left '' (W : Set P.left)
  have hF : IsOpen F := q.left.isOpenMap W W.isOpen
  let Z : Set A.X.left := Fᶜ
  refine ⟨Z, hF.isClosed_compl, fun x => ?_⟩
  constructor
  · intro hx
    change pt A x ∉ F
    rintro ⟨p, hpW, hpx⟩
    have hxc : IsClosed {pt A x} :=
      ((pointEquivClosedPoint A.X.hom) ⟨x.left, Over.w x⟩).2
    let T : Set P.left := (W : Set P.left) ∩ q.left ⁻¹' {pt A x}
    have hn : T.Nonempty := ⟨p, hpW, hpx⟩
    have hlc : IsLocallyClosed T := W.isOpen.isLocallyClosed.inter
      (hxc.preimage q.left.continuous).isLocallyClosed
    obtain ⟨z, hzT, hzc⟩ := nonempty_inter_closedPoints hn hlc
    let z0 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P :=
      Over.homMk (pointOfClosedPoint P.hom z hzc) (pointOfClosedPoint_comp P.hom z hzc)
    let d := z0 ≫ fst R A.X ≫ j
    let a := z0 ≫ q
    have hapt : pt A a = pt A x := by
      simpa only [a, z0, pt, Over.comp_left, Over.homMk_left,
        Scheme.Hom.comp_apply, pointOfClosedPoint_apply] using hzT.2
    have ha : a = x := Over.OverMorphism.ext <|
      ext_of_apply_closedPoint_eq A.X.hom (Over.w a) (Over.w x) hapt
    have hd : pt A d ∈ D.support := by
      change I.subschemeι ((z0 ≫ fst R A.X).left (IsLocalRing.closedPoint K)) ∈ D.support
      rw [← ZInQ.Contrib.CloudR2NOS.Step1.range_subschemeι_vanishingIdeal D.support]
      exact ⟨_, rfl⟩
    have hdm : pt A (d * a) = m.left z := by
      have h : z0 ≫ m = d * a := by
        dsimp only [m, d, a]
        rw [MonObj.comp_mul]
      rw [← h]
      simp only [z0, pt, Over.comp_left, Over.homMk_left,
        Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
    have hgood : m.left z ∈ D.support := by
      rw [← hdm, ha]
      exact hx d hd
    exact hzT.1 hgood
  · intro hx d hd
    change pt A x ∉ F at hx
    have hr : Set.range d.left.base ⊆ D.support := by
      rintro _ ⟨z, rfl⟩
      rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
      exact hd
    let dl : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ R :=
      Over.homMk (ZInQ.Contrib.CloudR2NOS.Step1.liftToReduced D.support d.left hr) (by
        change ZInQ.Contrib.CloudR2NOS.Step1.liftToReduced D.support d.left hr ≫
          I.subschemeι ≫ A.X.hom = _
        rw [← Category.assoc, ZInQ.Contrib.CloudR2NOS.Step1.liftToReduced_fac]
        exact Over.w d)
    have hdl : dl ≫ j = d := Over.OverMorphism.ext <|
      ZInQ.Contrib.CloudR2NOS.Step1.liftToReduced_fac D.support d.left hr
    let z0 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ P := lift dl x
    have hq : q.left (z0.left (IsLocalRing.closedPoint K)) = pt A x := by
      simp only [q, z0, pt, ← Scheme.Hom.comp_apply, ← Over.comp_left, lift_snd]
    have hm : m.left (z0.left (IsLocalRing.closedPoint K)) = pt A (d * x) := by
      have h : z0 ≫ m = d * x := by
        dsimp only [z0, m, q]
        rw [MonObj.comp_mul, ← Category.assoc, lift_fst, hdl, lift_snd]
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, h]
      rfl
    by_contra hbad
    apply hx
    exact ⟨z0.left (IsLocalRing.closedPoint K), by change m.left _ ∉ D.support; rwa [hm], hq⟩

/-- The full rational stabilizer is a closed subset of SAME A. The inverse
parameter supplies the missing direction, not an invalid forward-only group. -/
theorem exists_closed_support_stabilizer
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData) :
    ∃ Z : Set A.X.left, IsClosed Z ∧
      ∀ x : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X,
        x ∈ supportPointStabilizer A D ↔ pt A x ∈ Z := by
  obtain ⟨F, hF, hiff⟩ := exists_closed_forward_locus A D
  let Z : Set A.X.left := F ∩ ι[A.X].left ⁻¹' F
  refine ⟨Z, hF.inter (hF.preimage ι[A.X].left.continuous), fun x => ?_⟩
  rw [stabilizer_iff_forward_inverse, hiff, hiff]
  change (pt A x ∈ F ∧ pt A x⁻¹ ∈ F) ↔
    (pt A x ∈ F ∧ ι[A.X].left (pt A x) ∈ F)
  have hi : pt A x⁻¹ = ι[A.X].left (pt A x) := by
    change (x.left ≫ ι[A.X].left) (IsLocalRing.closedPoint K) = _
    exact Scheme.Hom.comp_apply _ _ _
  rw [hi]

/-- Actual proper closed Y with ALL rational points inside affine U is
finite. This is the native complete-coset obstruction, with no smoothness
or dimension hypothesis on the internally extracted Y. -/
theorem finite_of_closed_immersion_points_in_affine_open
    {K : Type u} [Field K] [IsAlgClosed K]
    (A Y : Grp (Over (Spec (CommRingCat.of K))))
    [ZInQ.Contrib.CloudR2NOS.Step1.IsProperIntegralGroup Y]
    (j : Y.X ⟶ A.X) (hj : IsClosedImmersion j.left)
    (U : A.X.left.Opens) (hU : IsAffineOpen U)
    (hpoints : ∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y.X, pt A (y ≫ j) ∈ U) :
    IsFinite Y.X.hom := by
  haveI : IsClosedImmersion j.left := hj
  haveI : IsProper Y.X.hom := ZInQ.Contrib.CloudR2NOS.Step1.IsProperIntegralGroup.proper
  let T : Set Y.X.left := j.left ⁻¹' (U : Set A.X.left)ᶜ
  have hT : IsClosed T := U.isOpen.isClosed_compl.preimage j.left.continuous
  have hsub : T ⊆ (∅ : Set Y.X.left) :=
    H5OriginalDVR.Lane5.GM3Points.subset_of_closedPoint_subset Y.X.hom T ∅ hT isClosed_empty (by
      intro z hz hzc
      let y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y.X :=
        Over.homMk (pointOfClosedPoint Y.X.hom z hzc) (pointOfClosedPoint_comp Y.X.hom z hzc)
      have hgood : j.left z ∈ U := by
        simpa only [y, pt, Over.comp_left, Over.homMk_left,
          Scheme.Hom.comp_apply, pointOfClosedPoint_apply] using hpoints y
      exact False.elim (hz hgood))
  have hrange : Set.range j.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    by_contra hz
    exact (hsub hz).elim
  let jl := IsOpenImmersion.lift U.ι j.left hrange
  have hpb : IsPullback jl (𝟙 Y.X.left) U.ι j.left :=
    IsOpenImmersion.isPullback_lift_id j.left U.ι hrange
  haveI : IsClosedImmersion jl := MorphismProperty.of_isPullback hpb.flip hj
  haveI : IsAffine U.toScheme := hU
  haveI : IsAffine Y.X.left := isAffine_of_isAffineHom jl
  exact (IsFinite.iff_isProper_and_isAffineHom (f := Y.X.hom)).mpr ⟨inferInstance, inferInstance⟩

/-- Affine complement containing the actual identity has a FINITE rational
support stabilizer. Reuses C3's native generic E3 term, not a new extracted
model or an assumed finite-kernel/ample Fact. -/
theorem supportPointStabilizer_finite_of_affine_complement
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData) (U : A.X.left.Opens) (hU : IsAffineOpen U)
    (hunit : pt A 1 ∈ U) (hsupp : (D.support : Set A.X.left) = (U : Set A.X.left)ᶜ) :
    (supportPointStabilizer A D).Finite := by
  by_contra hinf
  obtain ⟨Z, hZ, hiff⟩ := exists_closed_support_stabilizer A D
  have h1 : (1 : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ A.X) ∈ supportPointStabilizer A D :=
    fun d => by simp only [mul_one]
  have hmul : ∀ x y, x ∈ supportPointStabilizer A D → y ∈ supportPointStabilizer A D →
      x * y ∈ supportPointStabilizer A D := by
    intro x y hx hy d
    exact (hx d).trans (by simpa only [mul_assoc] using hy (d * x))
  have hinv : ∀ x, x ∈ supportPointStabilizer A D → x⁻¹ ∈ supportPointStabilizer A D := by
    intro x hx d
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using (hx (d * x⁻¹)).symm
  obtain ⟨Y, hY, j, hjm, hj, hnot, hpoints⟩ :=
    ZInQ.Contrib.CloudR2NOS.Step1.infiniteClosedSubgroupContainsIntegral_proved
      A Z hZ (supportPointStabilizer A D) hiff h1 hmul hinv hinf
  letI := hY
  letI := hjm
  have hinside : ∀ y : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ Y.X, pt A (y ≫ j) ∈ U := by
    intro y
    have hs := hpoints y
    have he : pt A 1 ∉ D.support := by
      change pt A 1 ∉ (D.support : Set A.X.left)
      rw [hsupp]
      exact not_not.mpr hunit
    have hn : pt A (y ≫ j) ∉ D.support := by
      intro hd
      exact he ((hs 1).mpr (by simpa only [one_mul] using hd))
    change pt A (y ≫ j) ∉ (D.support : Set A.X.left) at hn
    rw [hsupp] at hn
    exact not_not.mp hn
  exact hnot (finite_of_closed_immersion_points_in_affine_open A Y j hj U hU hinside)

/-- The ORIGINAL IDEAL H(D) is contained in the finite support stabilizer.
No support-preserving translation is falsely declared ideal-preserving. -/
theorem divisorStabilizer_finite_of_affine_complement
    {K : Type u} [Field K] [IsAlgClosed K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A]
    (D : A.X.left.IdealSheafData) (U : A.X.left.Opens) (hU : IsAffineOpen U)
    (hunit : pt A 1 ∈ U) (hsupp : (D.support : Set A.X.left) = (U : Set A.X.left)ᶜ) :
    (H5OriginalDVR.Lane2.NativeDivisorKernel.divisorStabilizer A D).Finite := by
  apply (supportPointStabilizer_finite_of_affine_complement A D U hU hunit hsupp).subset
  intro x hx d
  have h : (D.comap (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x)).support =
      D.support := congrArg Scheme.IdealSheafData.support hx
  have hd := congrArg (fun S : Closeds A.X.left => pt A d ∈ S) h
  rw [Scheme.IdealSheafData.support_comap] at hd
  change (H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x (pt A d) ∈ D.support) =
    (pt A d ∈ D.support) at hd
  have happ : H5OriginalDVR.Lane2.NativeDivisorKernel.rightTranslation A x (pt A d) =
      pt A (d * x) := H5OriginalDVR.Lane2.NativeTranslationAction.rightTranslation_apply_point A x d
  exact (eq_iff_iff.mp (happ ▸ hd)).symm

end H5OriginalDVR.Lane2.NativeAffineComplementStabilizer
