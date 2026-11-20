/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Mathlib.LinearAlgebra.TensorProduct.Tower
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.Modules.exists_linearEquiv_sections_baseChange_of_locallyTrivial
    {R : Type u} [CommRing R] {X : Scheme.{u}} (c : X ⟶ Spec (.of R)) (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.Opens) (hU : IsAffineOpen U) (A : Type u) [CommRing A] [Algebra R A] :
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom c M U
    letI := Scheme.TwoAffineOpenCover.moduleSectionsOfHom
      (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R A))
      ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M)
      ((Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ U)
    ∃ e : A ⊗[R] Γ(M, U) ≃ₗ[A]
        Γ((Scheme.Modules.pullback (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).obj M,
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A)) ⁻¹ᵁ U),
      ∀ m : Γ(M, U), e ((1 : A) ⊗ₜ[R] m) =
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (Limits.pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app U).hom m := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_linearEquiv_sections_baseChange_of_locallyTrivial.solution
