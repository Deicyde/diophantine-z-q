/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_idealSheafData_tensor_linearEquiv_of_presentation
    {X : Scheme.{u}} [IsIntegral X] (M : X.Modules) (hM : Scheme.Modules.IsInvertible M)
    (φ : ∀ U : X.Opens, Γ(M, U) →+ (X.functionField : Type u))
    (hφ : (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ(M, U), φ V (M.presheaf.map (homOfLE h).op m) = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ(M, U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U))) :
    ∃ (I J : X.IdealSheafData)
      (e : ∀ U : X.affineOpens, ↥(I.ideal U) ⊗[Γ(X, U)] Γ(M, U) ≃ₗ[Γ(X, U)] ↥(J.ideal U)),
      (∀ (U : X.affineOpens) [Nonempty U] (a : Γ(X, U)),
          a ∈ I.ideal U ↔ ∀ m : Γ(M, U), ∃ b : Γ(X, U),
            algebraMap Γ(X, U) X.functionField b = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.affineOpens, Nonempty U → I.ideal U ≠ ⊥ ∧ J.ideal U ≠ ⊥) ∧
      (∀ (U : X.affineOpens) [Nonempty U] (a : ↥(I.ideal U)) (m : Γ(M, U)),
          algebraMap Γ(X, U) X.functionField (e U (a ⊗ₜ m) : Γ(X, U)) =
            algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ (U V : X.affineOpens) (h : (V : X.Opens) ≤ U) (a : ↥(I.ideal U)) (m : Γ(M, U)),
          X.presheaf.map (homOfLE h).op (e U (a ⊗ₜ m) : Γ(X, U)) =
            e V (⟨X.presheaf.map (homOfLE h).op a, I.ideal_le_comap_ideal h a.2⟩ ⊗ₜ
              M.presheaf.map (homOfLE h).op m)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_idealSheafData_tensor_linearEquiv_of_presentation.solution
