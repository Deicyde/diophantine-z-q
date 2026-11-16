/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
    {R : Type u} [CommRing R] [IsDomain R] (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Kbar : Type u) [Field Kbar] [Algebra K Kbar] [IsAlgClosure K Kbar] [Algebra R Kbar] [IsScalarTower R K Kbar]
    {Y X : Scheme.{u}} {gY : Y ⟶ Spec (CommRingCat.of R)} {gX : X ⟶ Spec (CommRingCat.of R)}
    [Flat gY] [LocallyOfFiniteType gY] [IsReduced Y] [IsSeparated gX]
    (φ ψ : SchemeHomOver gY gX)
    (h : ∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R Kbar))) gY, x.1 ≫ φ.1 = x.1 ≫ ψ.1) :
    φ = ψ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat.solution
