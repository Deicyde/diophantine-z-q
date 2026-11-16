/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_mul_pow_le_cechFinrank_zero_tensorPow. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_mul_pow_le_cechFinrank_zero_tensorPow

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_forall_mul_pow_le_cechFinrank_zero_tensorPow
    {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)} [IsIntegral X]
    (d : ℕ) (hd : (d : WithBot ℕ∞) ≤ topologicalKrullDim X)
    {𝓛 : X.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) {N : ℕ} (𝔓 : 𝓛.ProjPresentation f N)
    (hfin : IsFinite 𝔓.toProj) :
    ∃ c : ℚ, 0 < c ∧ ∀ (n : ℕ) (𝒦 : X.OrderedAffineCover),
      c * (n : ℚ) ^ d ≤ ((OModulePresheaf.ofModules f (𝓛.tensorPow n)).cechFinrank 𝒦 0 : ℚ) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_mul_pow_le_cechFinrank_zero_tensorPow.solution
