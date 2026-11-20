/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_isLocalization_basicOpen
    {R : CommRingCat.{u}} (M : (Spec (.of R)).Modules)
    (hloc : ∀ g : Γ(Spec (.of R), ⊤),
      (∀ x : Γ(M, (Spec (.of R)).basicOpen g), ∃ (n : ℕ) (y : Γ(M, ⊤)),
          M.presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op y
            = ((Spec (.of R)).presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op).hom (g ^ n) • x)
        ∧ (∀ y : Γ(M, ⊤), M.presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n) • y = 0)) :
    IsIso M.fromTildeΓ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen.solution
