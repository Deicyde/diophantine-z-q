import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ToricEvaluation

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace PicDict.Transport

variable {X Y P : Scheme.{0}}

private theorem composedFrame_congr {u v : X ⟶ Y} (huv : u = v) (i : Y ⟶ P) (z : X ⟶ P)
    (M : P.Modules) (α : unit Y ≅ (pullback i).obj M) (hu : u ≫ i = z) (hv : v ≫ i = z) :
    pullFrame u α ≪≫ (pullbackComp u i).app M ≪≫ (pullbackCongr hu).app M =
      pullFrame v α ≪≫ (pullbackComp v i).app M ≪≫ (pullbackCongr hv).app M := by
  subst huv
  rfl

theorem evalFrameOnComposite_commuting (j : X ⟶ Y) (i : Y ⟶ P)
    (a' : X ⟶ X) (a : Y ⟶ Y) (l : P ⟶ P)
    (ha : j ≫ a = a' ≫ j) (hl : i ≫ l = a ≫ i) (M : P.Modules)
    (α : unit Y ≅ (pullback i).obj M) :
    evalFrameOnComposite j i a l hl M α =
      frameOnComposite (j ≫ i) a' l
        (show (j ≫ i) ≫ l = a' ≫ (j ≫ i) by
          rw [Category.assoc, hl, ← Category.assoc, ha, Category.assoc])
        M (pullFrame j α ≪≫ (pullbackComp j i).app M) := by
  rw [evalFrameOnComposite_eq]
  have he := composedFrame_congr ha i ((j ≫ i) ≫ l) M α
    (by simp only [Category.assoc, hl])
    (by rw [← ha]; simp only [Category.assoc, hl])
  rw [he]
  apply Iso.ext
  simp only [frameOnComposite, pullFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, pullbackCongr_hom_app]
  rw [reassoc_of% (pullbackComp_assoc_app a' j i M)]
  have e := congrArg Iso.hom (pullFrame_comp a' j α)
  simp only [pullFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] at e
  rw [reassoc_of% e]
  simp

/-- Restriction of a comparison defect along commuting diagonal
multiplications is itself the comparison defect, in the pulled-back frame. -/
theorem pullUnitIso_comparisonDefect_commuting (j : X ⟶ Y) (i : Y ⟶ P)
    (a' b' : X ⟶ X) (a b : Y ⟶ Y) (l r : P ⟶ P)
    (ha : j ≫ a = a' ≫ j) (hb : j ≫ b = b' ≫ j)
    (hl : i ≫ l = a ≫ i) (hr : i ≫ r = b ≫ i)
    (M : P.Modules) (J : (pullback l).obj M ≅ (pullback r).obj M)
    (α : unit Y ≅ (pullback i).obj M) :
    pullUnitIso j (comparisonDefect i a b l r hl hr M J α) =
      comparisonDefect (j ≫ i) a' b' l r
        (by rw [Category.assoc, hl, ← Category.assoc, ha, Category.assoc])
        (by rw [Category.assoc, hr, ← Category.assoc, hb, Category.assoc])
        M J (pullFrame j α ≪≫ (pullbackComp j i).app M) := by
  rw [pullUnitIso_comparisonDefect,
    evalFrameOnComposite_commuting j i a' a l ha hl,
    evalFrameOnComposite_commuting j i b' b r hb hr]
  rfl

end PicDict.Transport

#print axioms PicDict.Transport.pullUnitIso_comparisonDefect_commuting
