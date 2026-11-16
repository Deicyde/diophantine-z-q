/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_res_basicOpen_eq
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} {F : OModulePresheaf π}
    (hF : F.IsQuasicoherent) (U : V.affineOpens) {ι : Type*} [Fintype ι] (h : ι → Γ(V, U.1))
    (hcov : U.1 ≤ ⨆ j, V.basicOpen (h j)) (x : ∀ j, F.obj (V.basicOpen (h j)))
    (hx : ∀ j k, F.res ((V.basicOpen_mul (h j) (h k)).trans_le inf_le_left) (x j) =
      F.res ((V.basicOpen_mul (h j) (h k)).trans_le inf_le_right) (x k)) :
    ∃ y : F.obj U.1, ∀ j, F.res (V.basicOpen_le (h j)) y = x j := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_res_basicOpen_eq.solution
