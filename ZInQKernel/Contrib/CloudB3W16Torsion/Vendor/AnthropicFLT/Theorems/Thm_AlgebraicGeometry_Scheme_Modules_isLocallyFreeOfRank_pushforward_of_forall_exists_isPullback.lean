/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesLocallyFreeOfRank
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback
    {X T : Scheme.{u}} (π : X ⟶ T) (F : X.Modules) (n : ℕ)
    (h : ∀ y : T, ∃ (W : T.Opens), y ∈ W ∧ ∃ (W' X' : Scheme.{u}) (e : W' ≅ W.toScheme) (π' : X' ⟶ W')
      (g' : X' ⟶ X), IsPullback g' π' π (e.hom ≫ W.ι) ∧
        Scheme.Modules.IsLocallyFreeOfRank n
          ((Scheme.Modules.pushforward π').obj ((Scheme.Modules.pullback g').obj F))) :
    Scheme.Modules.IsLocallyFreeOfRank n ((Scheme.Modules.pushforward π).obj F) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocallyFreeOfRank_pushforward_of_forall_exists_isPullback.solution
