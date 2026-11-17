/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
theorem AlgebraicGeometry.Scheme.Modules.exists_projPresentation_of_iSup_eq_top
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (M : X.Modules)
    (N : ℕ) (σ : Fin (N + 1) → Γ(M, ⊤))
    (U : Fin (N + 1) → X.Opens) (hU : iSup U = ⊤)
    (hframe : ∀ i (V : X.Opens), V ≤ U i →
       Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ i) : Γ(M, V))) :
    ∃ 𝔓 : M.ProjPresentation f N, 𝔓.σ = σ ∧ ∀ i, U i ≤ 𝔓.toProj ⁻¹ᵁ Proj.basicOpen _ (MvPolynomial.X i) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_projPresentation_of_iSup_eq_top.solution
