import ZInQKernel.Contrib.OneProof.SZThm33.ValuationGenericFibre
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ModelSlice

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit SmoothGroup PicDict HDec.WeilPairing ZInQ.ToricOrthogonality
open scoped CategoryTheory.MonObj

namespace SZRaynaud.Ambient

section BaseChange

variable {S T : Scheme.{0}} (u : T ⟶ S)

theorem pullbackMap_fst {X Y : Over S} (f : X ⟶ Y) :
    ((Over.pullback u).map f).left ≫ pullback.fst Y.hom u =
      pullback.fst X.hom u ≫ f.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

variable {X Y : Over S} [GrpObj X] [GrpObj Y]

local instance : GrpObj ((Over.pullback u).obj X) := Functor.grpObjObj

private def pullbackSection (x : 𝟙_ (Over S) ⟶ X) :
    𝟙_ (Over T) ⟶ (Over.pullback u).obj X :=
  Functor.LaxMonoidal.ε (Over.pullback u) ≫ (Over.pullback u).map x

omit [GrpObj X] in
private theorem pullbackSection_fst (x : 𝟙_ (Over S) ⟶ X) :
    (pullbackSection u x).left ≫ pullback.fst X.hom u = u ≫ x.left := by
  let v := Functor.LaxMonoidal.ε (Over.pullback u)
  have hv : v.left ≫ pullback.snd (𝟙_ (Over S)).hom u = 𝟙 T := Over.w v
  have hs : pullback.fst (𝟙_ (Over S)).hom u = pullback.snd (𝟙_ (Over S)).hom u ≫ u :=
    (Category.comp_id _).symm.trans pullback.condition
  change (v.left ≫ ((Over.pullback u).map x).left) ≫ _ = _
  simp only [Category.assoc, pullbackMap_fst, hs, reassoc_of% hv]
  exact Category.id_comp _

private theorem pullback_translateBy (x : 𝟙_ (Over S) ⟶ X) :
    (Over.pullback u).map (translateBy X x) =
      translateBy ((Over.pullback u).obj X) (pullbackSection u x) := by
  simp only [translateBy, pullbackSection, Functor.map_mul,
    Functor.map_comp, ← Functor.Monoidal.toUnit_ε, Category.assoc]
  rw [(Over.pullback u).map_id]

private theorem pullback_multiplyBy (n : ℕ) :
    (Over.pullback u).map (multiplyBy X n) = multiplyBy ((Over.pullback u).obj X) n := by
  change (Over.pullback u).map ((𝟙 X) ^ n) = (𝟙 ((Over.pullback u).obj X)) ^ n
  calc
    _ = ((Over.pullback u).map (𝟙 X)) ^ n :=
      map_pow (Functor.homMonoidHom (Over.pullback u)) (𝟙 X) n
    _ = _ := congrArg (· ^ n) ((Over.pullback u).map_id X)

end BaseChange

private theorem translateBy_comp_groupHom {S : Scheme.{0}} {X Y : Over S}
    [GrpObj X] [GrpObj Y] (f : X ⟶ Y) [IsMonHom f] (x : 𝟙_ (Over S) ⟶ X) :
    translateBy X x ≫ f = f ≫ translateBy Y (x ≫ f) := by
  simp only [translateBy, MonObj.mul_comp, MonObj.comp_mul, Category.id_comp, Category.comp_id,
    Category.assoc]
  rw [← Category.assoc f (toUnit Y), toUnit_unique (f ≫ toUnit Y) (toUnit X)]

private theorem multiplyBy_comp_groupHom {S : Scheme.{0}} {X Y : Over S}
    [GrpObj X] [GrpObj Y] (f : X ⟶ Y) [IsMonHom f] (n : ℕ) :
    multiplyBy X n ≫ f = f ≫ multiplyBy Y n := by
  simp only [multiplyBy, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]

section Generic

variable {K : Type} [Field K] {O : ValuationSubring K} {w : ValuationSubring (AlgebraicClosure K)}
  (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O) (A : PkgI3.AbVar K)
  (M : GroupModelO A O)

local instance : GrpObj ((Over.pullback (gen (w := w))).obj (valuationModel hw A M)) := Functor.grpObjObj

set_option backward.isDefEq.respectTransparency false in
private theorem valuationGenericIso_point (x : Over.mk (base hw) ⟶ M.G) :
    pts (genPtHom hw A M (restrictPoint gen x)) ≫ (valuationGenericIso hw A M).hom =
      pullbackSection gen (valuationSectionEquiv hw A M x) := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change _ ≫ valuationGenericMap hw A M =
      (pullbackSection gen (valuationSectionEquiv hw A M x)).left ≫ pullback.fst (valuationModel hw A M).hom gen
    exact (valuationGenericMap_point hw A M x).trans (pullbackSection_fst gen _).symm
  · exact (Over.w _).trans (Over.w _).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Generic translation in the Weil formula agrees with translation by the
valuation section restricting to that geometric point. -/
theorem valuationGenericMap_translate (x : Over.mk (base hw) ⟶ M.G) :
    trl (genPtHom hw A M (restrictPoint gen x)) ≫ valuationGenericMap hw A M =
      valuationGenericMap hw A M ≫ (translateBy (valuationModel hw A M) (valuationSectionEquiv hw A M x)).left := by
  let e := valuationGenericIso hw A M
  let y := valuationSectionEquiv hw A M x
  let z := genPtHom hw A M (restrictPoint gen x)
  have : IsMonHom e.hom := valuationGenericIso_isMonHom hw A M
  have ht : (translateBy (bcX A) (pts z)).left = trl z := tr_pts z
  have h := translateBy_comp_groupHom e.hom (pts z)
  rw [show pts z ≫ e.hom = pullbackSection gen y from valuationGenericIso_point hw A M x,
    ← pullback_translateBy] at h
  have hl := congrArg Over.Hom.left h
  simp only [Over.comp_left] at hl
  change trl z ≫ (e.hom.left ≫ pullback.fst (valuationModel hw A M).hom gen) =
    (e.hom.left ≫ pullback.fst (valuationModel hw A M).hom gen) ≫ (translateBy (valuationModel hw A M) y).left
  rw [← ht, ← Category.assoc, hl, Category.assoc, pullbackMap_fst, ← Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
/-- Multiplication in the Weil formula agrees with multiplication on the valuation model. -/
theorem valuationGenericMap_multiply (n : ℕ) :
    mlN A n ≫ valuationGenericMap hw A M = valuationGenericMap hw A M ≫ (multiplyBy (valuationModel hw A M) n).left := by
  let e := valuationGenericIso hw A M
  have : IsMonHom e.hom := valuationGenericIso_isMonHom hw A M
  have h := multiplyBy_comp_groupHom e.hom n
  rw [← pullback_multiplyBy (X := (valuationModel hw A M)) gen n] at h
  have hl := congrArg Over.Hom.left h
  simp only [Over.comp_left] at hl
  have hm : (multiplyBy (bcX A) n).left = mlN A n := mul_AKbar A n
  change mlN A n ≫ (e.hom.left ≫ pullback.fst (valuationModel hw A M).hom gen) =
    (e.hom.left ≫ pullback.fst (valuationModel hw A M).hom gen) ≫ (multiplyBy (valuationModel hw A M) n).left
  rw [← hm, ← Category.assoc, hl, Category.assoc, pullbackMap_fst, ← Category.assoc]

end Generic
end SZRaynaud.Ambient
