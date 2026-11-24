import ZInQKernel.Contrib.OneProof.SZThm33.ValuationGenericActions

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit SmoothGroup PicDict PicDict.DirectPairing ZInQ.ToricOrthogonality
open scoped CategoryTheory.MonObj

namespace SZRaynaud.Ambient

variable {K : Type} [Field K] {O : ValuationSubring K} {w : ValuationSubring (AlgebraicClosure K)}
  (hw : w.comap (algebraMap K (AlgebraicClosure K)) = O) (A : PkgI3.AbVar K)
  (M : GroupModelO A O)

private abbrev modelProjection : (valuationModel hw A M).left ⟶ M.G.left :=
  pullback.fst M.G.hom (base hw)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
/-- The slice of the relative polarization on the valuation model has the
translation-difference class of the pullback of the original model line. -/
theorem valuationSliceClass
    (y : 𝟙_ (Over (Spec (CommRingCat.of w))) ⟶ (valuationModel hw A M)) (L : (M.G).left.Pic)
    (a : (valuationModel hw A M).left ⟶ ((M.G) ⊗ (M.G)).left)
    (hfst : a ≫ (fst (M.G) (M.G)).left = (modelProjection hw A M))
    (hsnd : a ≫ (snd (M.G) (M.G)).left = (valuationModel hw A M).hom ≫ y.left ≫ (modelProjection hw A M)) :
    Scheme.Pic.map a (productDeltaClass (M.G) L) =
      Scheme.Pic.map (translateBy (valuationModel hw A M) y).left (Scheme.Pic.map (modelProjection hw A M) L) * (Scheme.Pic.map (modelProjection hw A M) L)⁻¹ := by
  let F := Over.pullback (base hw)
  let f := Functor.LaxMonoidal.μ F (M.G) (M.G)
  let p := f.left ≫ pullback.fst ((M.G) ⊗ (M.G)).hom (base hw)
  have hf : p ≫ (fst (M.G) (M.G)).left = (fst (valuationModel hw A M) (valuationModel hw A M)).left ≫ (modelProjection hw A M) := by
    dsimp only [p]
    rw [Category.assoc, ← pullbackMap_fst (base hw) (fst (M.G) (M.G)), ← Category.assoc, ← Over.comp_left]
    exact congrArg (fun e : (valuationModel hw A M) ⊗ (valuationModel hw A M) ⟶
          (valuationModel hw A M) => e.left ≫ (modelProjection hw A M))
      (Functor.Monoidal.μ_fst F (M.G) (M.G))
  have hs : p ≫ (snd (M.G) (M.G)).left = (snd (valuationModel hw A M) (valuationModel hw A M)).left ≫ (modelProjection hw A M) := by
    dsimp only [p]
    rw [Category.assoc, ← pullbackMap_fst (base hw) (snd (M.G) (M.G)), ← Category.assoc, ← Over.comp_left]
    exact congrArg (fun e : (valuationModel hw A M) ⊗ (valuationModel hw A M) ⟶
          (valuationModel hw A M) => e.left ≫ (modelProjection hw A M))
      (Functor.Monoidal.μ_snd F (M.G) (M.G))
  have hp : Scheme.Pic.map p (productDeltaClass (M.G) L) = productDeltaClass (valuationModel hw A M) (Scheme.Pic.map (modelProjection hw A M) L) := by
    unfold productDeltaClass
    rw [Scheme.Pic.map_comp, map_deltaClass_baseChange, map_deltaClass]
    exact congrArg₂ (fun a b : (valuationModel hw A M) ⊗ (valuationModel hw A M) ⟶
          (valuationModel hw A M) => deltaClass a b (Scheme.Pic.map (modelProjection hw A M) L))
      (Functor.Monoidal.μ_fst F (M.G) (M.G)) (Functor.Monoidal.μ_snd F (M.G) (M.G))
  have ha : a = (pointSlice (valuationModel hw A M) y).left ≫ p := by
    apply pullback.hom_ext
    · change a ≫ (fst (M.G) (M.G)).left = ((pointSlice (valuationModel hw A M) y).left ≫ p) ≫ (fst (M.G) (M.G)).left
      rw [Category.assoc, hf, ← Category.assoc, ← Over.comp_left, pointSlice, lift_fst,
        Over.id_left, Category.id_comp]
      exact hfst
    · change a ≫ (snd (M.G) (M.G)).left = ((pointSlice (valuationModel hw A M) y).left ≫ p) ≫ (snd (M.G) (M.G)).left
      rw [Category.assoc, hs, ← Category.assoc, ← Over.comp_left, pointSlice, lift_snd,
        Over.comp_left, Over.toUnit_left, Category.assoc]
      exact hsnd
  have : Subsingleton (Spec (CommRingCat.of w)).Pic := Scheme.Pic.subsingleton_spec_localRing w
  rw [ha, Scheme.Pic.map_comp, hp, map_productDeltaClass_pointSlice]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
/-- The generic restriction of the model's normalized polarization slice
is the precise Picard class used by the direct Weil pairing. -/
theorem valuationGenericSlice_pic
    (z : Over.mk (base hw) ⟶ (M.G))
    (L : (M.G).left.Modules) [SheafOfModules.IsInvertible L]
    (D : ((M.G) ⊗ (M.G)).left.Modules) [SheafOfModules.IsInvertible D]
    (hD : Scheme.Pic.mk D = productDeltaClass (M.G) (Scheme.Pic.mk L))
    (a : (valuationModel hw A M).left ⟶ ((M.G) ⊗ (M.G)).left)
    (hfst : a ≫ (fst (M.G) (M.G)).left = (modelProjection hw A M))
    (hsnd : a ≫ (snd (M.G) (M.G)).left = (valuationModel hw A M).hom ≫ (valuationSectionEquiv hw A M z).left ≫ (modelProjection hw A M)) :
    letI : SheafOfModules.IsInvertible (Relative.genericModelLine M L) := by
      unfold Relative.genericModelLine
      infer_instance
    Scheme.Pic.mk ((Scheme.Modules.pullback (valuationGenericMap hw A M)).obj
      ((Scheme.Modules.pullback a).obj D)) =
      polarization A (Scheme.Pic.mk (Relative.genericModelLine M L))
        (genPtHom hw A M (restrictPoint gen z)) := by
  let y := valuationSectionEquiv hw A M z
  let x := genPtHom hw A M (restrictPoint gen z)
  let g := valuationGenericMap hw A M
  let t := (translateBy (valuationModel hw A M) y).left
  let δ : (valuationModel hw A M).left.Pic := Scheme.Pic.map (modelProjection hw A M) (Scheme.Pic.mk L)
  have : SheafOfModules.IsInvertible (Relative.genericModelLine M L) := by
    unfold Relative.genericModelLine
    infer_instance
  let Lη := Scheme.Pic.mk (Relative.genericModelLine M L)
  have hslice : Scheme.Pic.map a (Scheme.Pic.mk D) = Scheme.Pic.map t δ * δ⁻¹ :=
    (congrArg (Scheme.Pic.map a) hD).trans (valuationSliceClass hw A M y (Scheme.Pic.mk L) a hfst hsnd)
  have h0 : Scheme.Pic.map g δ = bcPic A Lη := by
    change Scheme.Pic.map g (Scheme.Pic.map (modelProjection hw A M) _) = _
    rw [← Scheme.Pic.map_comp]
    exact valuationGenericMap_modelLine hw A M L
  have h1 : Scheme.Pic.map g (Scheme.Pic.map t δ) = Scheme.Pic.map (trl x) (bcPic A Lη) := by
    have ht : trl x ≫ g = g ≫ t := valuationGenericMap_translate hw A M z
    rw [← Scheme.Pic.map_comp, ← ht, Scheme.Pic.map_comp, h0]
  change Scheme.Pic.mk ((Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback a).obj D)) =
    polarization A Lη x
  calc
    _ = Scheme.Pic.map g (Scheme.Pic.map a (Scheme.Pic.mk D)) :=
      (Scheme.Pic.map_mk g _).symm.trans (congrArg (Scheme.Pic.map g) (Scheme.Pic.map_mk a D).symm)
    _ = phiPt (bcPic A Lη) x := by
      rw [hslice]
      change (Scheme.Pic.mapHom g) (Scheme.Pic.map t δ * δ⁻¹) = _
      rw [map_mul, map_inv]
      change Scheme.Pic.map g (Scheme.Pic.map t δ) * (Scheme.Pic.map g δ)⁻¹ = _
      rw [h1, h0]
      rfl
    _ = _ := (polarization_apply A Lη x).symm

end SZRaynaud.Ambient
