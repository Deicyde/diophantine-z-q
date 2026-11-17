/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_pullback
    {X X' : Scheme.{u}} (p : X' ⟶ X) (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (m : Γ(M, ⊤)) (z : X')
    (h : ∃ U' : X'.Opens, z ∈ U' ∧ ∀ V' : X'.Opens, V' ≤ U' →
      Function.Bijective fun g : Γ(X', V') =>
        g • (((Scheme.Modules.pullback p).obj M).presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op
          ((((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app M).app ⊤) m) :
            Γ((Scheme.Modules.pullback p).obj M, V'))) :
    ∃ U : X.Opens, p z ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op m : Γ(M, V)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_pullback.solution
