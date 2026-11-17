import ZInQKernel.Contrib.CloudR2Poincare.L1.NativeCohomologyLocus
import ZInQKernel.Contrib.CloudR2Poincare.L1.SectionsTriviality
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.Sections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Proper

/-!
# Native topological seesaw closedness

For a proper flat geometrically integral family over a noetherian affine base,
the set of parameters where an invertible sheaf is trivial on the residue fibre
is closed. This is the native W07 counterpart of Stacks Cube.SeesawClosed:287.
It is deliberately labelled TOPOLOGICAL: it does not reconstruct the universal
closed subgroup scheme, whose nilpotent test-scheme behaviour is additional.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2Poincare.L1

open Scheme

/-- For a proper finitely presented coefficient sheaf, positive residue H⁰-rank
means nonzero ACTUAL global sections on that fibre. -/
theorem higherDirectImageResidueRank_zero_pos_iff_globalSections
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (M : X.Modules) [M.IsFinitePresentation] (y : Y) :
    0 < higherDirectImageResidueRank f M 0 y ↔
      Nontrivial Γ((Modules.pullback (pullback.fst f (Y.fromSpecResidueField y))).obj M, ⊤) := by
  let p := Y.fromSpecResidueField y
  let Xy := pullback f p
  let fy := pullback.snd f p
  let My := (Modules.pullback (pullback.fst f p)).obj M
  letI : Xy.Over (Spec (Y.residueField y)) := ⟨fy⟩
  haveI : IsProper (Xy ↘ Spec (Y.residueField y)) := by change IsProper fy; infer_instance
  haveI : My.IsFinitePresentation := inferInstance
  have hfinite := Modules.hasFiniteH_of_isProper fy My
  haveI : Module.Finite (Y.residueField y) (My.H 0) := hfinite 0
  haveI := Modules.isGrothendieckAbelian Xy
  obtain ⟨e⟩ := Modules.nonempty_moduleSpecΓFunctor_obj_higherDirectImage_linearEquiv_H
    My (Y.residueField y) 0
  change 0 < Module.finrank (Y.residueField y)
      ((moduleSpecΓFunctor (R := Y.residueField y)).obj
        ((Modules.higherDirectImage fy 0).obj My)) ↔ Nontrivial Γ(My, ⊤)
  let e' : ((moduleSpecΓFunctor (R := Y.residueField y)).obj
      ((Modules.higherDirectImage fy 0).obj My)) ≃ₗ[Y.residueField y] My.H 0 := e
  rw [e'.finrank_eq]
  constructor
  · intro h
    haveI : Nontrivial (My.H 0) := Module.nontrivial_of_finrank_pos h
    exact (Modules.H.zeroLinearEquiv My).toEquiv.symm.nontrivial
  · intro h
    haveI := h
    haveI : Nontrivial (My.H 0) := (Modules.H.zeroLinearEquiv My).toEquiv.nontrivial
    exact Module.finrank_pos

/-- A normalized family's fibre is trivial iff the class of its actual pullback is one. -/
theorem fibrePicardClass_eq_one_iff_iso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : X.Modules) [M.IsInvertible] (y : Y) :
    Pic.map (pullback.fst f (Y.fromSpecResidueField y)) (Pic.mk M) = 1 ↔
      Nonempty ((Modules.pullback (pullback.fst f (Y.fromSpecResidueField y))).obj M ≅
        Modules.unit (pullback f (Y.fromSpecResidueField y))) := by
  rw [Pic.map_mk, Pic.one_eq_mk_unit]
  exact Pic.mk_eq_mk_iff _ _

/-- The native residue-fibre triviality locus is topologically closed (all dimensions). -/
theorem isClosed_fibrePicardClass_trivial
    (R : Type u) [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible] :
    IsClosed {y : Spec (.of R) |
      Pic.map (pullback.fst f ((Spec (.of R)).fromSpecResidueField y)) (Pic.mk M) = 1} := by
  haveI : M.IsFinitePresentation := inferInstance
  haveI : Mᵛ.IsFinitePresentation := inferInstance
  have hflatM : M.IsFlatOver f := Modules.isFlatOver_of_isInvertible f M
  have hflatD : Mᵛ.IsFlatOver f := Modules.isFlatOver_of_isInvertible f Mᵛ
  have hM := isClosed_higherDirectImageResidueRank_ge R f M hflatM 0 1
  have hD := isClosed_higherDirectImageResidueRank_ge R f Mᵛ hflatD 0 1
  convert hM.inter hD using 1
  ext y
  rw [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_ofPred_eq,
    fibrePicardClass_eq_one_iff_iso]
  let p := (Spec (.of R)).fromSpecResidueField y
  let fy := pullback.snd f p
  let My := (Modules.pullback (pullback.fst f p)).obj M
  haveI : IsProper fy := inferInstance
  haveI : GeometricallyIntegral fy := inferInstance
  rw [nonempty_iso_unit_iff_nontrivial_globalSections fy My]
  have hdual : Nontrivial Γ((Modules.pullback (pullback.fst f p)).obj Mᵛ, ⊤) ↔
      Nontrivial Γ(Myᵛ, ⊤) := by
    let e := Modules.appLinearEquivOfIso (Modules.pullbackDualIso (pullback.fst f p) M) ⊤
    exact ⟨fun h ↦ by haveI := h; exact e.toEquiv.symm.nontrivial,
      fun h ↦ by haveI := h; exact e.toEquiv.nontrivial⟩
  rw [← hdual, ← higherDirectImageResidueRank_zero_pos_iff_globalSections f M y,
    ← higherDirectImageResidueRank_zero_pos_iff_globalSections f Mᵛ y]
  omega

end ZInQ.Contrib.CloudR2Poincare.L1
