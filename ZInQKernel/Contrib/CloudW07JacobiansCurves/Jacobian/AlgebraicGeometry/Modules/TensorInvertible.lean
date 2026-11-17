-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Modules.TensorInvertible), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.PullbackMonoidal

/-!
# Tensor products of invertible module sheaves

A tensor product of two locally free module sheaves of rank one is locally free
of rank one. The trivializations are obtained on intersections of the two
trivializing covers, using compatibility of pullback with tensor product.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {scheme : Scheme.{schemeUniverse}}

/-- The tensor unit is the invertible structure sheaf. -/
instance isInvertible_tensorUnit : (𝟙_ scheme.Modules).IsInvertible :=
  inferInstanceAs ((SheafOfModules.unit scheme.ringCatSheaf).IsInvertible)

/-- The tensor product of two invertible module sheaves is invertible. -/
instance isInvertible_tensorObj (moduleSheaf targetSheaf : scheme.Modules)
    [invertible : moduleSheaf.IsInvertible] [targetInvertible : targetSheaf.IsInvertible] :
    (moduleSheaf ⊗ targetSheaf).IsInvertible := by
  refine (isInvertible_iff_forall_exists_pullback_unit _).2 fun point ↦ ?_
  obtain ⟨firstOpen, firstMembership, ⟨firstTrivialization⟩⟩ := invertible.exists_isoUnit point
  obtain ⟨secondOpen, secondMembership, ⟨secondTrivialization⟩⟩ :=
    targetInvertible.exists_isoUnit point
  refine ⟨firstOpen ⊓ secondOpen, ⟨firstMembership, secondMembership⟩, ?_⟩
  have restrictTrivialization (sheaf : scheme.Modules) {openSubset : scheme.Opens}
      (inclusion : firstOpen ⊓ secondOpen ≤ openSubset)
      (trivialization : (pullback openSubset.ι).obj sheaf ≅ SheafOfModules.unit _) :
      Nonempty ((pullback (firstOpen ⊓ secondOpen).ι).obj sheaf ≅ SheafOfModules.unit _) :=
    ⟨(pullbackCongr (scheme.homOfLE_ι inclusion).symm).app sheaf ≪≫
      (pullbackComp _ _).symm.app sheaf ≪≫
      (pullback (scheme.homOfLE inclusion)).mapIso trivialization ≪≫ pullbackObjUnitIso _⟩
  obtain ⟨firstIso⟩ := restrictTrivialization moduleSheaf inf_le_left firstTrivialization
  obtain ⟨secondIso⟩ := restrictTrivialization targetSheaf inf_le_right secondTrivialization
  exact ⟨pullbackTensorObjIso (firstOpen ⊓ secondOpen).ι moduleSheaf targetSheaf ≪≫
    (firstIso ⊗ᵢ secondIso) ≪≫ λ_ _⟩

end AlgebraicGeometry.Scheme.Modules
