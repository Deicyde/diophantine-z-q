import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsConstructible
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Kernel
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Group.Translations
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! A dominant morphism of algebraic groups over an algebraically closed field
is surjective on rational points. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open Topology TopologicalSpace
open ZInQ.Contrib.MilneQuasiInverse.Kernel

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace ZInQ.FaltingsRestate

variable {k : Type} [Field k] [IsAlgClosed k]
local notation "Sch" => Over (Spec (CommRingCat.of k))
local notation "Pt" => 𝟙_ Sch

set_option backward.isDefEq.respectTransparency false in
/-- A rational point in the set-theoretic image of a locally finite-type map
over an algebraically closed field lifts to a rational point. -/
theorem exists_point_preimage_of_in_range
    {X Y : Sch} (f : X ⟶ Y) [LocallyOfFiniteType f.left]
    (b : Pt ⟶ Y) (hb : b.left (IsLocalRing.closedPoint k) ∈ Set.range f.left) :
    ∃ a : Pt ⟶ X, a ≫ f = b := by
  let a₀ := pullback.fst f.left b.left
  let s := pullback.snd f.left b.left
  haveI : LocallyOfFiniteType s :=
    show LocallyOfFiniteType (pullback.snd f.left b.left) by infer_instance
  have hpre : IsLocalRing.closedPoint k ∈ Set.range s := by
    change IsLocalRing.closedPoint k ∈ Set.range (pullback.snd f.left b.left)
    rwa [Scheme.Pullback.range_snd]
  obtain ⟨w, hw⟩ := hpre
  haveI : JacobsonSpace (𝟙_ Sch).left := inferInstanceAs (JacobsonSpace (PrimeSpectrum k))
  haveI : JacobsonSpace (pullback f.left b.left : Scheme) :=
    LocallyOfFiniteType.jacobsonSpace s
  have hwC : w ∈ closure (closedPoints (pullback f.left b.left : Scheme)) := by
    rw [closure_closedPoints]
    exact Set.mem_univ _
  obtain ⟨z, _, hz⟩ := mem_closure_iff.mp hwC Set.univ isOpen_univ (Set.mem_univ _)
  let a := pointOfClosedPoint s z hz
  have ha : a ≫ s = 𝟙 _ := pointOfClosedPoint_comp s z hz
  have he : (a ≫ a₀) ≫ f.left = b.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha, Category.id_comp]
  refine ⟨Over.homMk (a ≫ a₀) ?_, Over.OverMorphism.ext he⟩
  rw [← Over.w f, ← Category.assoc, he, Over.w b]

set_option backward.isDefEq.respectTransparency false in
/-- A dominant morphism of algebraic groups over an algebraically closed field
is surjective on rational points. -/
theorem surjective_points_of_dominant_group_hom
    {X Y : Sch} [GrpObj X] [GrpObj Y] [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] (f : X ⟶ Y) [IsMonHom f] [QuasiCompact f.left]
    [IsDominant f.left] : Function.Surjective (pointsMap f Pt) := by
  haveI : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp _ Y.hom
  haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  haveI : LocallyOfFinitePresentation f.left := inferInstance
  haveI : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  haveI : IsNoetherian Y.left := {}
  haveI : Nonempty Y.left := ⟨(η[Y]).left (IsLocalRing.closedPoint k)⟩
  have hC : IsConstructible (Set.range f.left) := by
    rw [← Set.image_univ]
    exact (f.left.isLocallyConstructible_image IsLocallyConstructible.univ).isConstructible
  let U := interior (Set.range f.left)
  have hU : U.Nonempty := nonempty_interior_of_dense_constructible hC f.left.denseRange
  intro y
  let tr := GrpObj.mulLeft Y y
  haveI : IsIso tr.left := GrpObj.isIso_mulLeft_left Y y
  have htrU : (tr.left ⁻¹' U).Nonempty := hU.preimage tr.left.surjective
  obtain ⟨z, hz⟩ := htrU
  have hzo : z ∈ closure (Set.range f.left) := by rw [f.left.denseRange.closure_eq]; exact Set.mem_univ _
  obtain ⟨_, hwU, x, rfl⟩ := mem_closure_iff.mp hzo _ (isOpen_interior.preimage tr.left.continuous) hz
  let V := (f.left ≫ tr.left) ⁻¹' U
  have hVo : IsOpen V := isOpen_interior.preimage (f.left ≫ tr.left).continuous
  have hxV : x ∈ V := hwU
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  have hxC : x ∈ closure (closedPoints X.left) := by rw [closure_closedPoints]; exact Set.mem_univ _
  obtain ⟨c, hcV, hc⟩ := mem_closure_iff.mp hxC V hVo hxV
  let a : Pt ⟶ X := Over.homMk (pointOfClosedPoint X.hom c hc) (pointOfClosedPoint_comp X.hom c hc)
  have ha : a.left (IsLocalRing.closedPoint k) = c :=
    pointOfClosedPoint_apply X.hom c hc _
  let b : Pt ⟶ Y := a ≫ f ≫ tr
  let c₀ : (𝟙_ Sch).left := IsLocalRing.closedPoint k
  have hb : b.left (IsLocalRing.closedPoint k) ∈ Set.range f.left := by
    change tr.left (f.left (a.left c₀)) ∈ Set.range f.left
    have ha' : a.left c₀ = c := ha
    rw [ha']
    exact interior_subset hcV
  obtain ⟨d, hd⟩ := exists_point_preimage_of_in_range f b hb
  have hmul : b = y * (a ≫ f) := by
    have ht : (a ≫ f) ≫ toUnit Y = 𝟙 (𝟙_ Sch) := toUnit_unique _ _
    change (a ≫ f) ≫ GrpObj.mulLeft Y y = _
    rw [GrpObj.mulLeft_eq_mul, MonObj.comp_mul, ← Category.assoc, ht,
      Category.id_comp, Category.comp_id]
  refine ⟨d / a, ?_⟩
  rw [map_div, show pointsMap f Pt d = b from hd, hmul]
  change (y * (a ≫ f)) / (a ≫ f) = y
  exact mul_div_cancel_right _ _

end ZInQ.FaltingsRestate
