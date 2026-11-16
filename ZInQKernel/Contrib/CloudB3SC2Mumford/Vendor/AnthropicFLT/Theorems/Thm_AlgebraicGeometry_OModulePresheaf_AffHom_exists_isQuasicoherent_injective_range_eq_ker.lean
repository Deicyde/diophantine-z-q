/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.AffHom.exists_isQuasicoherent_injective_range_eq_ker
    {A : Type u} [CommRing A] {P : Scheme.{u}} {q : P ⟶ Spec (CommRingCat.of A)}
    {G F : OModulePresheaf q} (hGq : G.IsQuasicoherent) (hFq : F.IsQuasicoherent)
    (θ : OModulePresheaf.AffHom G F) :
    ∃ (K : OModulePresheaf q) (ι : OModulePresheaf.AffHom K G),
      (IsLocallyNoetherian P → G.IsCoherent → K.IsCoherent) ∧ K.IsQuasicoherent ∧
      (∀ U : P.affineOpens, Function.Injective (ι.app U)) ∧
      (∀ U : P.affineOpens, LinearMap.range (ι.app U) = LinearMap.ker (θ.app U)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker.solution
