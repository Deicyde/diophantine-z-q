/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.OModulePresheaf.exists_cochain_baseChange_equiv_of_locallyTrivial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (.of R)) [IsSeparated π]
    (𝒰 : X.OrderedAffineCover) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (A : Type u) [CommRing A] [Algebra R A] :
    ∃ E : ∀ i : ℕ, A ⊗[R] (OModulePresheaf.ofModules π M).cochain 𝒰 i ≃ₗ[A]
        (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
          ((Scheme.Modules.pullback
            (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).cochain (𝒰.baseChange π A) i,
      (∀ i : ℕ, (E (i + 1)).toLinearMap ∘ₗ ((OModulePresheaf.ofModules π M).d 𝒰 i).baseChange A
        = (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
            ((Scheme.Modules.pullback
              (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).d (𝒰.baseChange π A) i
          ∘ₗ (E i).toLinearMap) ∧
      (∀ (i : ℕ) (a : A) (c : (OModulePresheaf.ofModules π M).cochain 𝒰 i) (s : 𝒰.Idx i),
        E i (a ⊗ₜ[R] c) s
          = a • (OModulePresheaf.ofModules (Limits.pullback.snd π (Scheme.TwoAffineOpenCover.specMap R A))
              ((Scheme.Modules.pullback
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).obj M)).res
              (𝒰.baseChange_inter_le π A s)
              ((((Scheme.Modules.pullbackPushforwardAdjunction
                (Limits.pullback.fst π (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app
                (𝒰.inter s)).hom (c s))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_cochain_baseChange_equiv_of_locallyTrivial.solution
