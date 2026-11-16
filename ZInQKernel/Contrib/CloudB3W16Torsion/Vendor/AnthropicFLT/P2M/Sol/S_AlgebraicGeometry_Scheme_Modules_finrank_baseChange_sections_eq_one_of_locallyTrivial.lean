/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_projective_sections_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_finite_sections_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_rankAtStalk_sections_eq_one_of_locallyTrivial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 16000000

noncomputable section

theorem solution
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) (K : Type u) [Field K] [Algebra Γ(X, U.1) K] :
    Module.finrank K (K ⊗[Γ(X, U.1)] Γ(M, U.1)) = 1 := by
  haveI := Scheme.Modules.projective_sections_of_locallyTrivial M htriv U
  haveI := Scheme.Modules.finite_sections_of_locallyTrivial M htriv U
  haveI : Module.Flat ↑Γ(X, U.1) ↑Γ(M, U.1) := inferInstance
  exact Module.finrank_baseChange_eq_one_of_rankAtStalk_eq_one
    (R := ↑Γ(X, U.1)) ↑Γ(M, U.1)
    (fun 𝔭 => Scheme.Modules.rankAtStalk_sections_eq_one_of_locallyTrivial M htriv U 𝔭) K

end
