/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Actual group construction on the SAME effective tensor-coequalizer scheme.
The canonical source descends multiplication/unit/inverse and proves the
laws; its law is rebundled by the real native group-object constructor.
The cartesian GROUP iso is then proved, preserving the original scheme
map q. q/hq/hco here are intermediate OUTPUTS of ProjConstruction, never
assumed effective/model inputs in a final NOS theorem.

Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2,
canonical H5 lane4 port. All licensed source/NOTICE/modification credits
remain in that source family; only this new same-object bridge is added.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.CartesianGroup
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.AbelianProperties
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.TensorTriple
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open TensorCofaces TensorNerve

variable {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
  [Module.FaithfullyFlat R R']
  (V : (Base R).Opens) (G : Grp (Over (Cover R'))) (A : Grp (Over V.toScheme))
  (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
    (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
  [Etale (baseMap R R')] (c : Base R)
  [Mono ((baseMap R R').fiberToSpecResidueField c)]
  (hV : ∀ z : Base R, z ∉ V → z = c)

/-- Actually construct a relative law on the already constructed scheme,
    and prove the SAME q is group-compatible through the native cartesian
    group isomorphism. No supplied relative-law/group-compatibility input. -/
theorem exists_group_on_effective_tensor_scheme
    (X : Scheme.{u}) (f : X ⟶ Base R) (q : G.X.left ⟶ X)
    (hq : IsPullback q G.X.hom f (baseMap R R'))
    (hco : projection1 (R := R) R' G ≫ q = projection2 R' V G A e c hV ≫ q) :
    ∃ (L : RelativeGroupLaw R f)
      (i : G ≅ (Over.pullback (baseMap R R')).mapGrp.obj (groupOfRelativeLaw L)),
      i.hom.hom.hom.left ≫ pullback.fst f (baseMap R R') = q := by
  obtain ⟨L, hL, hComm⟩ :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_comp_eq_mul_of_isPullback_of_faithfullyFlat
      R' f G.X.hom q hq (structure2 (R := R) R' G)
      (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
      (cartesian1 (R := R) R' G) (cartesian2 R' V G A e c hV) hco
      (ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp G)
      (ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp (group2 (R := R) R' G))
      (source_projection1_mul (R := R) R' G) (source_projection2_mul R' V G A e c hV)
  let i := cartesianGroupIso f G (baseMap R R') q hq L hL
  refine ⟨L, i, ?_⟩
  change hq.isoPullback.hom ≫ pullback.fst f (baseMap R R') = q
  exact hq.isoPullback_hom_fst

/-- The constructed scheme's smoothness/properness transfer to its SAME
    native group object. Geometric connectedness is handled separately
    through actual generic/special fibres; no stage-GC assumption is added. -/
theorem exists_proper_smooth_group_on_effective_tensor_scheme
    [Smooth G.X.hom] [IsProper G.X.hom]
    (X : Scheme.{u}) (f : X ⟶ Base R) (q : G.X.left ⟶ X)
    (hq : IsPullback q G.X.hom f (baseMap R R'))
    (hco : projection1 (R := R) R' G ≫ q = projection2 R' V G A e c hV ≫ q) :
    ∃ (L : RelativeGroupLaw R f)
      (i : G ≅ (Over.pullback (baseMap R R')).mapGrp.obj (groupOfRelativeLaw L)),
      i.hom.hom.hom.left ≫ pullback.fst f (baseMap R R') = q ∧
      Smooth (groupOfRelativeLaw L).X.hom ∧ IsProper (groupOfRelativeLaw L).X.hom := by
  obtain ⟨L, i, hi⟩ := exists_group_on_effective_tensor_scheme R' V G A e c hV X f q hq hco
  haveI : Surjective (baseMap R R') := by
    constructor
    exact PrimeSpectrum.comap_surjective_of_faithfullyFlat
  haveI : Flat (baseMap R R') := by
    rw [baseMap, HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  haveI : QuasiCompact (baseMap R R') := inferInstance
  exact ⟨L, i, hi, smooth_of_fpqc_isPullback hq, proper_of_fpqc_isPullback hq⟩

#print axioms exists_group_on_effective_tensor_scheme
#print axioms exists_proper_smooth_group_on_effective_tensor_scheme

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
