import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ProductFrameNormalization

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace PicDict.Transport

variable {W X Y G P : Scheme.{0}}

/-- Pull a frame on the ambient axis to the axis of the subscheme. -/
def externalAxisFrame (s : X ⟶ Y) (i : Y ⟶ P) (p : X ⟶ G) (a : G ⟶ P)
    (h : s ≫ i = p ≫ a) {M : P.Modules} (e : unit G ≅ (pullback a).obj M) :
    unit X ≅ (pullback s).obj ((pullback i).obj M) :=
  pullFramedAlong p a e ≪≫ (pullbackCongr h.symm).app M ≪≫ ((pullbackComp s i).app M).symm

theorem externalAxisFrame_transport
    (s : X ⟶ Y) (i : Y ⟶ P) (p : X ⟶ G) (a : G ⟶ P)
    (h : s ≫ i = p ≫ a) {M : P.Modules} (e : unit G ≅ (pullback a).obj M) :
    (externalAxisFrame s i p a h e ≪≫ (pullbackComp s i).app M) ≪≫
      (pullbackCongr h).app M = pullFramedAlong p a e := by
  apply Iso.ext
  simp [externalAxisFrame, pullbackCongr_hom_app]

theorem eval_externalAxisFrame
    (w : W ⟶ X) (s : X ⟶ Y) (i : Y ⟶ P) (p : X ⟶ G) (a : G ⟶ P)
    (h : s ≫ i = p ≫ a) {M : P.Modules} (e : unit G ≅ (pullback a).obj M) :
    pullFramedAlong w s (externalAxisFrame s i p a h e) ≪≫ (pullbackComp (w ≫ s) i).app M =
      pullFramedAlong (w ≫ p) a e ≪≫
        (pullbackCongr (show (w ≫ p) ≫ a = (w ≫ s) ≫ i by simp only [Category.assoc, h])).app M := by
  apply Iso.ext
  simp only [pullFramedAlong, pullFrame, externalAxisFrame, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.map_comp, Category.assoc,
    pullbackCongr_hom_app]
  rw [pullbackComp_assoc_inv₁ w s i M, reassoc_of% (map_eqToHom_comp_pullbackComp w h.symm M)]
  rw [reassoc_of% (pullbackComp_assoc_app w p a M)]
  have hwp := congrArg Iso.hom (pullFrame_comp w p e)
  simp only [pullFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] at hwp
  rw [reassoc_of% hwp]
  simp

private theorem frameMove {A B C : Scheme.{0}} {f g : A ⟶ B} (h : f = g)
    (i : B ⟶ C) (z : A ⟶ C) {M : C.Modules} (α : unit B ≅ (pullback i).obj M)
    (hf : f ≫ i = z) (hg : g ≫ i = z) :
    pullFramedAlong f i α ≪≫ (pullbackCongr hf).app M =
      pullFramedAlong g i α ≪≫ (pullbackCongr hg).app M := by
  subst h
  rfl

/-- Axis frames induced from compatible ambient frames agree at their common origin. -/
theorem externalAxisFrames_agree_at_origin {Q : Scheme.{0}}
    (s : X ⟶ Y) (t : Q ⟶ Y) (i : Y ⟶ P)
    (p : X ⟶ G) (q : Q ⟶ G) (a b : G ⟶ P)
    (hs : s ≫ i = p ≫ a) (ht : t ≫ i = q ≫ b)
    (x : W ⟶ X) (y : W ⟶ Q) (z : W ⟶ G) (hx : x ≫ p = z) (hy : y ≫ q = z)
    (hxy : x ≫ s = y ≫ t) (hz : z ≫ a = z ≫ b)
    {M : P.Modules} (e : unit G ≅ (pullback a).obj M) (d : unit G ≅ (pullback b).obj M)
    (he : pullFramedAlong z a e ≪≫ (pullbackCongr hz).app M = pullFramedAlong z b d) :
    pullFramedAlong x s (externalAxisFrame s i p a hs e) ≪≫
      (pullbackCongr hxy).app ((pullback i).obj M) =
        pullFramedAlong y t (externalAxisFrame t i q b ht d) := by
  apply Iso.ext
  rw [← cancel_mono ((pullbackComp (y ≫ t) i).hom.app M)]
  simp only [Iso.trans_hom, Iso.app_hom, Category.assoc, pullbackCongr_hom_app]
  rw [eqToHom_comp_pullbackComp hxy i M]
  rw [← Category.assoc]
  have h1 := congrArg Iso.hom (eval_externalAxisFrame x s i p a hs e)
  have h2 := congrArg Iso.hom (eval_externalAxisFrame y t i q b ht d)
  simp only [Iso.trans_hom, Iso.app_hom, pullbackCongr_hom_app] at h1 h2
  rw [h1, h2]
  simp only [Category.assoc, eqToHom_trans]
  let target := (y ≫ t) ≫ i
  have hxA : (x ≫ p) ≫ a = target := by simp only [target, Category.assoc, ← hs, ← Category.assoc x s i, hxy]
  have hyB : (y ≫ q) ≫ b = target := by simp only [target, Category.assoc, ht]
  have hx' : z ≫ a = target := (congrArg (· ≫ a) hx.symm).trans hxA
  have hy' : z ≫ b = target := (congrArg (· ≫ b) hy.symm).trans hyB
  have hx'' := congrArg Iso.hom (frameMove hx a target e hxA hx')
  have hy'' := congrArg Iso.hom (frameMove hy b target d hyB hy')
  simp only [Iso.trans_hom, Iso.app_hom, pullbackCongr_hom_app] at hx'' hy''
  rw [hx'', hy'']
  have he' := congrArg Iso.hom he
  simp only [Iso.trans_hom, Iso.app_hom, pullbackCongr_hom_app] at he'
  rw [← he']
  simp only [Category.assoc, eqToHom_trans]

end PicDict.Transport

#print axioms PicDict.Transport.externalAxisFrames_agree_at_origin
