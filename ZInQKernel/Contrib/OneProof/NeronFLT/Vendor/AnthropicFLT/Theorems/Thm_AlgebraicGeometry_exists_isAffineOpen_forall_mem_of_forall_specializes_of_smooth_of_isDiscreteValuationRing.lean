/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] [IsSeparated f] [QuasiCompact f] :
    ∃ U : X.Opens, IsAffineOpen U ∧
      ∀ x : X, (∀ y : X, y ⤳ x → f.base y = f.base x → y = x) → x ∈ U := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_isAffineOpen_forall_mem_of_forall_specializes_of_smooth_of_isDiscreteValuationRing.solution
