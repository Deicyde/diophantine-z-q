/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.eulerChar_eq_add_of_affSES
    {k : Type u} [Field k] {V : Scheme.{u}} {π : V ⟶ Spec (.of k)} [IsSeparated π]
    {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)
    (h₁ : F₁.CechFinite K) (h₂ : F₂.CechFinite K) (h₃ : F₃.CechFinite K) :
    F₂.eulerChar K = F₁.eulerChar K + F₃.eulerChar K := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_eulerChar_eq_add_of_affSES.solution
