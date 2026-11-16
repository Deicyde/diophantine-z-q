/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff
    {k : Type u} [Field k] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k)) (𝒱 : X.TwoAffineOpenCover)
    (M : X.Modules)
    (hM : ∀ p : X, ∃ U : X.Opens, p ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (k' : Type u) [Field k'] [Algebra k k'] :
    Module.finrank k'
        ((𝒱.pullback x k').sectionsOf (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k k'))
          ((Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k k'))).obj M)).H0 =
      Module.finrank k (𝒱.sectionsOf x M).H0 ∧
    (Subsingleton ((𝒱.pullback x k').sectionsOf (pullback.snd x (Scheme.TwoAffineOpenCover.specMap k k'))
          ((Scheme.Modules.pullback (pullback.fst x (Scheme.TwoAffineOpenCover.specMap k k'))).obj M)).H1 ↔
      Subsingleton (𝒱.sectionsOf x M).H1) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H0_sectionsOf_baseChange_eq_and_subsingleton_H1_iff.solution
