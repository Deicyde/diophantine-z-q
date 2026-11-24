import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.TwoAxisUnitIso

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace PicDict.Transport

variable {X Y P : Scheme.{0}}

/-- The frame induced by a commuting endomorphism square and a frame on
the subscheme. -/
def frameOnComposite (i : Y ⟶ P) (a : Y ⟶ Y) (l : P ⟶ P)
    (h : i ≫ l = a ≫ i) (M : P.Modules) (α : unit Y ≅ (pullback i).obj M) :
    unit Y ≅ (pullback (i ≫ l)).obj M :=
  pullFrame a α ≪≫ (pullbackComp a i).app M ≪≫ (pullbackCongr h.symm).app M

/-- Express a comparison on a subscheme whose restricted line is framed
as a unit automorphism. -/
def comparisonDefect (i : Y ⟶ P) (a b : Y ⟶ Y) (l r : P ⟶ P)
    (hl : i ≫ l = a ≫ i) (hr : i ≫ r = b ≫ i) (M : P.Modules)
    (J : (pullback l).obj M ≅ (pullback r).obj M)
    (α : unit Y ≅ (pullback i).obj M) : unit Y ≅ unit Y :=
  frameOnComposite i a l hl M α ≪≫ pullIsoAlong i l r M J ≪≫
    (frameOnComposite i b r hr M α).symm

/-- Pullback of the induced frame computes the original frame at the
composed endomorphism. -/
theorem pullFrame_frameOnComposite (x : X ⟶ Y) (i : Y ⟶ P) (a : Y ⟶ Y) (l : P ⟶ P)
    (h : i ≫ l = a ≫ i) (M : P.Modules) (α : unit Y ≅ (pullback i).obj M) :
    pullFrame x (frameOnComposite i a l h M α) ≪≫ (pullbackComp x (i ≫ l)).app M =
      pullFrame (x ≫ a) α ≪≫ (pullbackComp (x ≫ a) i).app M ≪≫
        (pullbackCongr (show (x ≫ a) ≫ i = x ≫ (i ≫ l) by rw [Category.assoc, h])).app M := by
  apply Iso.ext
  simp only [frameOnComposite, pullFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc, Functor.map_comp, pullbackCongr_hom_app]
  rw [map_eqToHom_comp_pullbackComp x h.symm M, reassoc_of% (pullbackComp_assoc_app x a i M)]
  have hc := congrArg Iso.hom (pullFrame_comp x a α)
  simp only [pullFrame, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc] at hc
  rw [reassoc_of% hc]
  simp

/-- When the comparison defect is a given scalar automorphism, the
comparison itself is the change between the two induced frames. -/
theorem pullIsoAlong_eq_of_comparisonDefect (i : Y ⟶ P) (a b : Y ⟶ Y) (l r : P ⟶ P)
    (hl : i ≫ l = a ≫ i) (hr : i ≫ r = b ≫ i) (M : P.Modules)
    (J : (pullback l).obj M ≅ (pullback r).obj M)
    (α : unit Y ≅ (pullback i).obj M) (u : unit Y ≅ unit Y)
    (hu : comparisonDefect i a b l r hl hr M J α = u) :
    pullIsoAlong i l r M J = (frameOnComposite i a l hl M α).symm ≪≫ u ≪≫
      frameOnComposite i b r hr M α := by
  apply Iso.ext
  rw [← hu]
  simp [comparisonDefect]

end PicDict.Transport

#print axioms PicDict.Transport.pullFrame_frameOnComposite
