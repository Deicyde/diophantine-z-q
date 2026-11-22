-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Scheme-theoretic density in an image

A quasi-compact morphism has scheme-theoretically dense image in its
scheme-theoretic image. Precomposition with a scheme-theoretically dominant
morphism preserves the kernel ideal sheaf.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

variable {sourceScheme targetScheme : Scheme.{u}} (morphism : sourceScheme ⟶ targetScheme)

lemma ker_toImage [QuasiCompact morphism] : morphism.toImage.ker = ⊥ := by
  refine IdealSheafData.ext_of_iSup_eq_top
    (fun affineOpen : targetScheme.affineOpens ↦
      ⟨morphism.imageι ⁻¹ᵁ affineOpen.1, affineOpen.2.preimage morphism.imageι⟩)
    ?_ fun affineOpen ↦ ?_
  · rw [← preimage_iSup, iSup_affineOpens_eq_top, preimage_top]
  · rw [ker_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (morphism.toImage_app_injective affineOpen)

instance isSchemeTheoreticallyDominant_toImage [QuasiCompact morphism] :
    IsSchemeTheoreticallyDominant morphism.toImage :=
  ⟨morphism.ker_toImage⟩

lemma ker_comp_of_isSchemeTheoreticallyDominant {intermediateScheme : Scheme.{u}}
    (denseMap : sourceScheme ⟶ intermediateScheme) (secondMap : intermediateScheme ⟶ targetScheme)
    [IsSchemeTheoreticallyDominant denseMap] : (denseMap ≫ secondMap).ker = secondMap.ker := by
  rw [ker_comp, denseMap.ker_eq_bot, IdealSheafData.map_bot]

/-- The scheme-theoretic image of a quasi-compact morphism has its expected underlying set. -/
lemma range_imageι [QuasiCompact morphism] :
    Set.range morphism.imageι = closure (Set.range morphism) := by
  rw [IdealSheafData.range_subschemeι, morphism.support_ker]

instance surjective_imageι [QuasiCompact morphism] [IsDominant morphism] :
    Surjective morphism.imageι :=
  ⟨Set.range_eq_univ.mp <| by rw [range_imageι, morphism.denseRange.closure_range]⟩

end AlgebraicGeometry.Scheme.Hom
