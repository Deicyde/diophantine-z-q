-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.GlobalSections.BaseChange), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.GlobalSections.Proper

/-!
# Base change of constant global functions

If a quasi-compact quasi-separated scheme over a field has only constant global
functions, its projection after base change induces an isomorphism on every
affine open of the new base.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe schemeUniverse

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {baseField : Type schemeUniverse} [Field baseField]
  {source : Scheme.{schemeUniverse}} [source.Over (Spec (.of baseField))]
  [CompactSpace source] [QuasiSeparatedSpace source]
  [IsIso (source ↘ Spec (.of baseField)).appTop]

/-- Constancy of global functions persists on affine opens after base change. -/
theorem isIso_app_of_isPullback_of_isIso_appTop
    {pulledSource base : Scheme.{schemeUniverse}} {sourceProjection : pulledSource ⟶ source}
    {projection : pulledSource ⟶ base} {baseMap : base ⟶ Spec (.of baseField)}
    (cartesian : IsPullback sourceProjection projection (source ↘ Spec (.of baseField)) baseMap)
    {openSubset : base.Opens} (affineOpen : IsAffineOpen openSubset) :
    IsIso (projection.app openSubset) := by
  have preimageEquation : projection ⁻¹ᵁ openSubset =
      sourceProjection ⁻¹ᵁ ⊤ ⊓ projection ⁻¹ᵁ openSubset := by simp
  have sectionIso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right cartesian
    (US := ⊤) (UT := openSubset) (UX := ⊤) le_top le_top preimageEquation
    (isAffineOpen_top _) affineOpen isCompact_univ isQuasiSeparated_univ
  have pushout := (isIso_pushoutSection_iff _ _ _ _).mp sectionIso
  have : IsIso ((source ↘ Spec (.of baseField)).appLE ⊤ ⊤ le_top) := by
    simpa [Hom.appTop, Hom.app_eq_appLE] using
      (inferInstance : IsIso (source ↘ Spec (.of baseField)).appTop)
  have := pushout.isIso_inr_of_isIso
  rw [Hom.app_eq_appLE]
  exact this

end AlgebraicGeometry.Scheme
