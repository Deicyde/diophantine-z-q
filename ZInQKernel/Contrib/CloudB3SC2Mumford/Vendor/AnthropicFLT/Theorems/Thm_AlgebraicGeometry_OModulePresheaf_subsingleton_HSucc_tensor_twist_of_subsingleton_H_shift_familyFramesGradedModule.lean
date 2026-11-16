/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule
    {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
    (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsAffineHom ι]
    {q : P ⟶ Spec (CommRingCat.of A)}
    (G : ℕ → OModulePresheaf q) (hq : ∀ k, (G k).IsQuasicoherent)
    {s : ℕ} (θ : Fin s → ∀ k : ℕ, OModulePresheaf.AffHom (G k) (G (k + 1))) (hθ : OModulePresheaf.YComm G θ)
    (d k i : ℕ)
    (hv : Subsingleton (ProjSpaceCech.GradedModule.H
      (ProjSpaceCech.GradedModule.shift (OModulePresheaf.familyFramesGradedModule ι G θ hθ) (d : ℤ)) (i + 1))) :
    Subsingleton (((G k).tensor (ProjSpace.twist q ι d)).HSucc (ProjSpace.stdCoverPullback ι) i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule.solution
