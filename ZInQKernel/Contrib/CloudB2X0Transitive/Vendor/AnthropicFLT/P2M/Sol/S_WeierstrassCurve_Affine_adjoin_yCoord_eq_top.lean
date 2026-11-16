/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_Affine_adjoin_yCoord_eq_top
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_WeierstrassCurve_Affine_adjoin_yCoord_eq_top

set_option autoImplicit false

open Polynomial WeierstrassCurve.Affine in
theorem solution {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} :
    IntermediateField.adjoin (RatFunc F) {WeierstrassCurve.Affine.yCoord W} = ⊤ := by
  rw [eq_top_iff]
  rintro z -
  have hpoly : ∀ p : F[X],
      polyToFunctionField W p ∈ IntermediateField.adjoin (RatFunc F) {yCoord W} := by
    intro p
    rw [← algebraMap_polynomial_eq_polyToFunctionField,
      IsScalarTower.algebraMap_apply F[X] (RatFunc F) W.FunctionField]
    exact IntermediateField.algebraMap_mem _ _
  have hcoord : ∀ r : W.CoordinateRing,
      algebraMap W.CoordinateRing W.FunctionField r
        ∈ IntermediateField.adjoin (RatFunc F) {yCoord W} := by
    intro r
    obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq r
    rw [algebraMap_smul_basis]
    exact add_mem (hpoly p)
      (mul_mem (hpoly q) (IntermediateField.mem_adjoin_simple_self _ _))
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := W.CoordinateRing) z
  rw [← hab]
  exact div_mem (hcoord a) (hcoord b)
