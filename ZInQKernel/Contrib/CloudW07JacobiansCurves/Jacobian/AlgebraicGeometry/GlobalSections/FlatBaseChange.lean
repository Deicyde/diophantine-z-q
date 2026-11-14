-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.GlobalSections.FlatBaseChange), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {base coverScheme scheme : Scheme.{schemeUniverse}} [IsAffine base] [IsAffine coverScheme] (coverMap : coverScheme ⟶ base) [Flat coverMap] (structureMap : scheme ⟶ base)
  [CompactSpace scheme] [QuasiSeparatedSpace scheme]

theorem isPushout_appTop_of_flat :
    IsPushout structureMap.appTop coverMap.appTop (pullback.fst structureMap coverMap).appTop (pullback.snd structureMap coverMap).appTop := by
  have comparisonIso : IsIso (pushoutSection (IsPullback.of_hasPullback structureMap coverMap) (US := ⊤) (UT := ⊤) (UX := ⊤)
      le_top le_top (UY := ⊤) (by simp)) :=
    isIso_pushoutSection_of_isQuasiSeparated_of_flat_right _ _ _ _ (isAffineOpen_top base)
      (isAffineOpen_top coverScheme) CompactSpace.isCompact_univ
      (isQuasiSeparated_univ_iff.mpr inferInstance)
  have := (isIso_pushoutSection_iff _ _ _ _).mp comparisonIso
  change IsPushout
    (structureMap.appTop ≫ scheme.presheaf.map (𝟙 (Opposite.op (⊤ : scheme.Opens))))
    (coverMap.appTop ≫ coverScheme.presheaf.map (𝟙 (Opposite.op (⊤ : coverScheme.Opens))))
    ((pullback.fst structureMap coverMap).appTop ≫
      (pullback structureMap coverMap).presheaf.map
        (𝟙 (Opposite.op (⊤ : (pullback structureMap coverMap).Opens))))
    ((pullback.snd structureMap coverMap).appTop ≫
      (pullback structureMap coverMap).presheaf.map
        (𝟙 (Opposite.op (⊤ : (pullback structureMap coverMap).Opens)))) at this
  simpa only [CategoryTheory.Functor.map_id, Category.comp_id] using this

end AlgebraicGeometry
