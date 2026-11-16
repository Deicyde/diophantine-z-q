/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem ProjSpaceCech.GradedModule.exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (M D : ProjSpaceCech.GradedModule R n) (hD : ProjSpaceCech.GradedModule.IsFG D)
    (h : ProjSpaceCech.GradedModule.Hom D M) (hinj : Function.Injective h.toLinearMap)
    (hsat : ∀ (e : ℤ) (f : M.M), f ∈ M.grade e → ∀ j : Fin (n + 1),
      ∃ (N : ℕ) (f' : D.M), f' ∈ D.grade (e + N) ∧ h.toLinearMap f' = (M.xMul j ^ N) f) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ i : ℕ, 1 ≤ i →
      Subsingleton (ProjSpaceCech.GradedModule.H (ProjSpaceCech.GradedModule.shift M d) i) := by p2m_exact_reverting @_root_.P2MW.S_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated.solution
