/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit
    {R : Type u} [CommRing R] {V W : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π]
    (γ : W ⟶ V) [IsAffineHom γ] (K : V.OrderedAffineCover) (N : V.Modules)
    (hN : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj N ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)) :
    Nonempty ((OModulePresheaf.ofModules (γ ≫ π) ((Scheme.Modules.pullback γ).obj N)).H0 (K.comap γ) ≃ₗ[R]
        ((OModulePresheaf.pushforwardUnit π γ).twist N).H0 K) ∧
      ∀ i : ℕ, Nonempty ((OModulePresheaf.ofModules (γ ≫ π) ((Scheme.Modules.pullback γ).obj N)).HSucc
          (K.comap γ) i ≃ₗ[R] ((OModulePresheaf.pushforwardUnit π γ).twist N).HSucc K i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit.solution
