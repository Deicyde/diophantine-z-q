/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem AlgebraicGeometry.RelPicard.nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) {r : ℕ}
    (P : Fin r → (Spec (CommRingCat.of k) ⟶ A)) (hP : ∀ i, P i ≫ a = 𝟙 _) :
    Nonempty ((prodKerGraph a P hP).invModule ⊗ ((RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ r).module ≅
      pointsSubBasepointModule (a := a) ε
        (List.ofFn fun i => (⟨P i, hP i⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule.solution
