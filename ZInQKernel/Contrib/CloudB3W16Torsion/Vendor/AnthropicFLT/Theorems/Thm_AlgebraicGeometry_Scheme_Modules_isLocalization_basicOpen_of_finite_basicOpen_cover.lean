/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_finite_basicOpen_cover
    {X : Scheme.{u}} (M : X.Modules) (U : X.affineOpens) (s : Finset Γ(X, U.1))
    (hs : U.1 ≤ ⨆ h ∈ s, X.basicOpen h)
    (hloc : ∀ h ∈ s, ∀ g : Γ(X, X.basicOpen h),
      ((∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, X.basicOpen h)),
          M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
        ∧ (∀ y : Γ(M, X.basicOpen h), M.presheaf.map (homOfLE (X.basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n : Γ(X, X.basicOpen h)) • y = 0)))
    (hloc₂ : ∀ h ∈ s, ∀ h' ∈ s, ∀ g : Γ(X, X.basicOpen h ⊓ X.basicOpen h'),
      ((∀ x : Γ(M, X.basicOpen g), ∃ (n : ℕ) (y : Γ(M, (X.basicOpen h ⊓ X.basicOpen h'))),
          M.presheaf.map (homOfLE (X.basicOpen_le g)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le g)).op (g ^ n) • x)
        ∧ (∀ y : Γ(M, (X.basicOpen h ⊓ X.basicOpen h')), M.presheaf.map (homOfLE (X.basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n : Γ(X, (X.basicOpen h ⊓ X.basicOpen h'))) • y = 0)))
    (f : Γ(X, U.1)) :
    ((∀ x : Γ(M, X.basicOpen f), ∃ (n : ℕ) (y : Γ(M, U.1)),
          M.presheaf.map (homOfLE (X.basicOpen_le f)).op y
            = X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ n) • x)
        ∧ (∀ y : Γ(M, U.1), M.presheaf.map (homOfLE (X.basicOpen_le f)).op y = 0 →
            ∃ n : ℕ, (f ^ n : Γ(X, U.1)) • y = 0)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isLocalization_basicOpen_of_finite_basicOpen_cover.solution
