import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ComparisonDefect

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace PicDict.Transport

variable {X Y P Z : Scheme.{0}}

/-- Evaluation of the induced frame at a test point of the subscheme. -/
def evalFrameOnComposite (x : X ⟶ Y) (i : Y ⟶ P) (a : Y ⟶ Y) (l : P ⟶ P)
    (h : i ≫ l = a ≫ i) (M : P.Modules) (α : unit Y ≅ (pullback i).obj M) :
    unit X ≅ (pullback ((x ≫ i) ≫ l)).obj M :=
  pullFrame x (frameOnComposite i a l h M α) ≪≫ (pullbackComp x (i ≫ l)).app M ≪≫
    (pullbackCongr (Category.assoc x i l).symm).app M

/-- The evaluated frame depends only on the multiplied subscheme point. -/
theorem evalFrameOnComposite_eq (x : X ⟶ Y) (i : Y ⟶ P) (a : Y ⟶ Y) (l : P ⟶ P)
    (h : i ≫ l = a ≫ i) (M : P.Modules) (α : unit Y ≅ (pullback i).obj M) :
    evalFrameOnComposite x i a l h M α =
      pullFrame (x ≫ a) α ≪≫ (pullbackComp (x ≫ a) i).app M ≪≫
        (pullbackCongr (show (x ≫ a) ≫ i = (x ≫ i) ≫ l by simp only [Category.assoc, h])).app M := by
  rw [evalFrameOnComposite, ← Iso.trans_assoc, pullFrame_frameOnComposite]
  apply Iso.ext
  simp [pullbackCongr_hom_app]

/-- Evaluating the comparison defect uses only the actual isomorphism
between the two pulled-back lines at the test point. -/
theorem pullUnitIso_comparisonDefect (x : X ⟶ Y) (i : Y ⟶ P) (a b : Y ⟶ Y) (l r : P ⟶ P)
    (hl : i ≫ l = a ≫ i) (hr : i ≫ r = b ≫ i) (M : P.Modules)
    (J : (pullback l).obj M ≅ (pullback r).obj M)
    (α : unit Y ≅ (pullback i).obj M) :
    pullUnitIso x (comparisonDefect i a b l r hl hr M J α) =
      evalFrameOnComposite x i a l hl M α ≪≫ pullIsoAlong (x ≫ i) l r M J ≪≫
        (evalFrameOnComposite x i b r hr M α).symm := by
  have hJ := pullIsoAlong_comp x i l r M J
  apply Iso.ext
  simp only [comparisonDefect, pullUnitIso, evalFrameOnComposite, pullFrame, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  have hJ' := congrArg Iso.hom hJ
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom,
    ] at hJ'
  have hm := congrArg (fun v => (pullbackComp x (i ≫ l)).hom.app M ≫ v ≫
    (pullbackComp x (i ≫ r)).inv.app M) hJ'
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app] at hm
  rw [reassoc_of% hm]
  simp [pullbackCongr_hom_app, pullbackCongr_inv_app]

private theorem conjugated_point_compare {p q : Z ⟶ P} (hpq : p = q) (B C : Z ⟶ P)
    (l r : P ⟶ P) (hBr : B = p ≫ r) (hCl : p ≫ l = C)
    (hBr' : B = q ≫ r) (hCl' : q ≫ l = C)
    (M : P.Modules) (J : (pullback l).obj M ≅ (pullback r).obj M) :
    (pullbackCongr hBr).app M ≪≫ (pullIsoAlong p l r M J).symm ≪≫
      (pullbackCongr hCl).app M =
    (pullbackCongr hBr').app M ≪≫ (pullIsoAlong q l r M J).symm ≪≫
      (pullbackCongr hCl').app M := by
  subst hpq
  rfl

/-- On a subscheme with a frame, evaluation of the slice trivialization
is evaluation of the multiplication comparison scalar followed by the
framing at the multiplied point. -/
theorem evalTriv_sliceComparison_on_framed_subscheme
    (s : Z ⟶ X) (x : Z ⟶ Y) (i : Y ⟶ P)
    (m : X ⟶ X) (a b : X ⟶ P) (l r : P ⟶ P)
    (hm : m ≫ a = a ≫ l) (hb : a ≫ r = b) (hx : x ≫ i = s ≫ a)
    (ml mr : Y ⟶ Y) (hl : i ≫ l = ml ≫ i) (hr : i ≫ r = mr ≫ i)
    (M : P.Modules) (J : (pullback l).obj M ≅ (pullback r).obj M)
    (α : unit Y ≅ (pullback i).obj M) (e : unit X ≅ (pullback b).obj M)
    (he : pullFrame s e ≪≫ (pullbackComp s b).app M ≪≫
      (pullbackCongr (show s ≫ b = (x ≫ i) ≫ r by rw [hx, Category.assoc, hb])).app M =
        evalFrameOnComposite x i mr r hr M α) :
    evalTriv s m ((pullback a).obj M) (sliceComparisonTriv m a b l r hm hb M J e) ≪≫
      (pullbackComp (s ≫ m) a).app M =
    (pullUnitIso x (comparisonDefect i ml mr l r hl hr M J α)).symm ≪≫
      evalFrameOnComposite x i ml l hl M α ≪≫
      (pullbackCongr (show (x ≫ i) ≫ l = (s ≫ m) ≫ a by
        rw [hx, Category.assoc, Category.assoc, hm])).app M := by
  rw [evalTriv_sliceComparison]
  have hcomp := conjugated_point_compare hx.symm (s ≫ b) ((s ≫ m) ≫ a) l r
    (by rw [Category.assoc, hb]) (by rw [Category.assoc, Category.assoc, hm])
    (by rw [hx, Category.assoc, hb]) (by rw [hx, Category.assoc, Category.assoc, hm]) M J
  rw [hcomp]
  have he' : ((pullFrame s e ≪≫ (pullbackComp s b).app M) ≪≫
      (pullbackCongr (show s ≫ b = (x ≫ i) ≫ r by rw [hx, Category.assoc, hb])).app M) =
        evalFrameOnComposite x i mr r hr M α := by
    rw [Iso.trans_assoc, he]
  rw [← Iso.trans_assoc ((pullbackComp s b).app M), ← Iso.trans_assoc (pullFrame s e),
    ← Iso.trans_assoc (pullFrame s e), he', pullUnitIso_comparisonDefect]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

end PicDict.Transport

#print axioms PicDict.Transport.evalTriv_sliceComparison_on_framed_subscheme
