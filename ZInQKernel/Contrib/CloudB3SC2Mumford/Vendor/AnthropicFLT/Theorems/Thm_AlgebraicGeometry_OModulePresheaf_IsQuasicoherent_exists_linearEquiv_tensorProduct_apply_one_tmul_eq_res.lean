/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res
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
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.IsQuasicoherent.exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res
    {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)} (G : OModulePresheaf π)
    (hG : G.IsQuasicoherent) (U V : X.affineOpens) (h : V.1 ≤ U.1) :
    letI := (X.presheaf.map (homOfLE h).op).hom.toAlgebra
    ∃ β : Γ(X, V.1) ⊗[Γ(X, U.1)] G.obj U.1 ≃ₗ[Γ(X, V.1)] G.obj V.1,
      ∀ x : G.obj U.1, β (1 ⊗ₜ x) = G.res h x := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_IsQuasicoherent_exists_linearEquiv_tensorProduct_apply_one_tmul_eq_res.solution
