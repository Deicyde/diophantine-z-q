/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_bijective_kerBaseChangeHom_and_surjective_unit_app_of_subsingleton_H1. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_bijective_kerBaseChangeHom_and_surjective_unit_app_of_subsingleton_H1

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.bijective_kerBaseChangeHom_and_surjective_unit_app_of_subsingleton_H1
    {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (.of R)) [IsProper c] [Flat c] (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (hfib : ∀ (K : Type u) [Field K] [Algebra R K],
      Subsingleton ((𝒱.pullback c K).sectionsOf (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((Scheme.Modules.pullback (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K))).obj M)).H1) :
    Module.Finite R (𝒱.sectionsOf c M).H0 ∧ Module.Projective R (𝒱.sectionsOf c M).H0 ∧
    (∀ (A : Type u) [CommRing A] [Algebra R A],
      Function.Bijective (TwoChartCech.kerBaseChangeHom (𝒱.sectionsOf c M).cechDiff A)) ∧
    (∀ (A : Type u) [CommRing A] [Algebra R A], Function.Surjective (algebraMap R A) →
      Function.Surjective
        (((Scheme.Modules.pullbackPushforwardAdjunction
          (pullback.fst c (Scheme.TwoAffineOpenCover.specMap R A))).unit.app M).app ⊤).hom) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_bijective_kerBaseChangeHom_and_surjective_unit_app_of_subsingleton_H1.solution
