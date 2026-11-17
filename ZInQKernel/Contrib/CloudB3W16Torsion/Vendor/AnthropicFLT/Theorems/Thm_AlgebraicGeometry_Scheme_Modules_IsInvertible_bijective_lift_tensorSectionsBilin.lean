/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.bijective_lift_tensorSectionsBilin
    {X : Scheme.{u}} {L M : X.Modules} (hL : Scheme.Modules.IsInvertible L)
    (hM : Scheme.Modules.IsInvertible M) (U : X.affineOpens) :
    Function.Bijective (TensorProduct.lift (Scheme.Modules.tensorSectionsBilin L M U) :
      Γ(L, U) ⊗[Γ(X, U)] Γ(M, U) →ₗ[Γ(X, U)] Γ(L ⊗ M, U)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_bijective_lift_tensorSectionsBilin.solution
