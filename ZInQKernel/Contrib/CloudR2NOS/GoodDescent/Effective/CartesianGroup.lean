/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Convert the real canonical relative group law on the SAME cartesian
scheme into a native Grp object and the actual base-change GROUP iso.
No arbitrary scheme-only iso is substituted, no group law/model exists
as a final NOS premise; the relative law is constructed by the source
fpqc group-law descent in GroupConstruction. Source nominal definitions
and the published H76 law-of-Grp are reused without duplication.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.RelativeLawProjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ZInQ.Contrib.CloudW03NeronSurj.FLT.NeronModelInfra
open ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- Native group on precisely `Over.mk f`, using the canonical constructed
    relative group law and its actual Yoneda group-object constructor. -/
def groupOfRelativeLaw {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) :
    Grp (Over (Spec (CommRingCat.of R))) where
  X := Over.mk f
  grp := L.grpObjOverMk

/-- Actual native multiplication is the given canonical relative law. -/
theorem groupOfRelativeLaw_point_mul {R : Type u} [CommRing R] {X : Scheme.{u}}
    {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x y : Over.mk t ⟶ (groupOfRelativeLaw L).X) :
    (x * y).left = (L.mul t (overHomToSchemeHomOver x) (overHomToSchemeHomOver y)).1 := by
  letI := L.grpObjOverMk
  exact congrArg Subtype.val (L.overHomToSchemeHomOver_mul t x y)

/-- A native group morphism is determined by the multiplication-preserving
    maps on ALL test schemes. Unit preservation follows from cancellation. -/
theorem isMonHom_of_point_mul {S : Scheme.{u}} (G H : Grp (Over S)) (f : G.X ⟶ H.X)
    (hm : ∀ (T : Over S) (a b : T ⟶ G.X), (a * b) ≫ f = (a ≫ f) * (b ≫ f)) : IsMonHom f := by
  have ho (T : Over S) : (1 : T ⟶ G.X) ≫ f = 1 := by
    let a : T ⟶ H.X := (1 : T ⟶ G.X) ≫ f
    have h : a * a = a * 1 := by
      have hh := hm T 1 1
      simpa only [one_mul, mul_one, a] using hh.symm
    exact mul_left_cancel h
  refine ⟨?_, ?_⟩
  · change η[G.X] ≫ f = η[H.X]
    rw [MonObj.one_eq_one, MonObj.one_eq_one, ho]
  · change μ[G.X] ≫ f = (f ⊗ₘ f) ≫ μ[H.X]
    rw [MonObj.mul_eq_mul, MonObj.mul_eq_mul, hm, MonObj.comp_mul]
    exact congrArg₂ (fun x y : G.X ⊗ G.X ⟶ H.X => x * y)
      (tensorHom_fst f f).symm (tensorHom_snd f f).symm

section Cartesian
variable {R R' : Type u} [CommRing R] [CommRing R']
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
  (G : Grp (Over (Spec (CommRingCat.of R'))))
  (p : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
  (c : G.X.left ⟶ X) (hc : IsPullback c G.X.hom f p)
  (L : RelativeGroupLaw R f)
  (hL : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
    (x y : SchemeHomOver t G.X.hom),
    ((ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp G).mul t x y).1 ≫ c =
      (L.mul (t ≫ p)
        ⟨x.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, x.2]⟩
        ⟨y.1 ≫ c, by rw [Category.assoc, hc.w, ← Category.assoc, y.2]⟩).1)

/-- The actual cartesian underlying iso, directed from the old model to
    the base change of the newly constructed native group. -/
def cartesianSchemeIso : G.X ≅ ((Over.pullback p).mapGrp.obj (groupOfRelativeLaw L)).X :=
  Over.isoMk hc.isoPullback (by
    change hc.isoPullback.hom ≫ pullback.snd f p = G.X.hom
    exact hc.isoPullback_hom_snd)

include hL

private theorem cartesian_mul_points (T : Over (Spec (CommRingCat.of R')))
    (x y : T ⟶ G.X) :
    pointMapOver (groupOfRelativeLaw L) G p c hc.w T.hom (x * y) =
      pointMapOver (groupOfRelativeLaw L) G p c hc.w T.hom x *
        pointMapOver (groupOfRelativeLaw L) G p c hc.w T.hom y := by
  apply Over.OverMorphism.ext
  change (x * y).left ≫ c =
    (pointMapOver (groupOfRelativeLaw L) G p c hc.w T.hom x *
      pointMapOver (groupOfRelativeLaw L) G p c hc.w T.hom y).left
  rw [groupOfRelativeLaw_point_mul]
  exact hL T.hom (overHomToSchemeHomOver x) (overHomToSchemeHomOver y)

/-- Genuine group hom on every test scheme, induced by the actual cartesian
    comparison and the CONSTRUCTED native relative-law group. -/
def cartesianPointHom (T : Over (Spec (CommRingCat.of R'))) :
    (T ⟶ G.X) →* (T ⟶ ((Over.pullback p).mapGrp.obj (groupOfRelativeLaw L)).X) := by
  let F := pointMapOver (groupOfRelativeLaw L) G p c hc.w T.hom
  have hm (x y : T ⟶ G.X) : F (x * y) = F x * F y := cartesian_mul_points f G p c hc L hL T x y
  have ho : F (1 : T ⟶ G.X) = 1 := by
    have h : F (1 : T ⟶ G.X) * F 1 = F 1 * 1 := by
      simpa only [one_mul, mul_one] using (hm 1 1).symm
    exact mul_left_cancel h
  let C : (T ⟶ G.X) →* ((Over.map p).obj T ⟶ (groupOfRelativeLaw L).X) :=
    { toFun := F, map_one' := ho, map_mul' := hm }
  exact (GroupPoints.pullbackPts p T (groupOfRelativeLaw L)).toMonoidHom.comp C

/-- The constructed test-point hom is literally postcomposition with the
    original cartesian scheme isomorphism. -/
theorem cartesianPointHom_eq_postcomp (T : Over (Spec (CommRingCat.of R'))) (x : T ⟶ G.X) :
    cartesianPointHom f G p c hc L hL T x = x ≫ (cartesianSchemeIso f G p c hc L).hom := by
  let y : (Over.map p).obj T ⟶ (groupOfRelativeLaw L).X := pointMapOver (groupOfRelativeLaw L) G p c hc.w T.hom x
  let a : T.left ⟶ G.X.left := x.left
  let z : T.left ⟶ pullback f p := (cartesianPointHom f G p c hc L hL T x).left
  let r : G.X.left ⟶ pullback f p := (cartesianSchemeIso f G p c hc L).hom.left
  have hz₁ : z ≫ pullback.fst f p = a ≫ c :=
    GroupPoints.pullbackPts_fst p T (groupOfRelativeLaw L) y
  have hz₂ : z ≫ pullback.snd f p = T.hom := GroupPoints.pullbackPts_snd p T (groupOfRelativeLaw L) y
  have hr₁ : r ≫ pullback.fst f p = c := hc.isoPullback_hom_fst
  have hr₂ : r ≫ pullback.snd f p = G.X.hom := hc.isoPullback_hom_snd
  have hx : a ≫ G.X.hom = T.hom := by
    have h := Over.w x
    change a ≫ G.X.hom = T.hom at h
    exact h
  have hraw : z = a ≫ r := by
    apply pullback.hom_ext
    · rw [Category.assoc, hr₁]
      exact hz₁
    · rw [Category.assoc, hr₂]
      exact hz₂.trans hx.symm
  apply Over.OverMorphism.ext
  exact hraw

/-- Actual IsMonHom of the SAME cartesian iso. -/
theorem cartesianSchemeIso_isMonHom : IsMonHom (cartesianSchemeIso f G p c hc L).hom := by
  apply isMonHom_of_point_mul G ((Over.pullback p).mapGrp.obj (groupOfRelativeLaw L))
  intro T x y
  rw [← cartesianPointHom_eq_postcomp f G p c hc L hL,
    ← cartesianPointHom_eq_postcomp f G p c hc L hL,
    ← cartesianPointHom_eq_postcomp f G p c hc L hL]
  exact map_mul (cartesianPointHom f G p c hc L hL T) x y

/-- Constructed base-change GROUP iso, preserving the same scheme map c. -/
def cartesianGroupIso : G ≅ (Over.pullback p).mapGrp.obj (groupOfRelativeLaw L) := by
  haveI := cartesianSchemeIso_isMonHom f G p c hc L hL
  exact Grp.mkIso' (cartesianSchemeIso f G p c hc L)

end Cartesian

#print axioms groupOfRelativeLaw
#print axioms groupOfRelativeLaw_point_mul
#print axioms isMonHom_of_point_mul
#print axioms cartesianSchemeIso_isMonHom
#print axioms cartesianGroupIso

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
