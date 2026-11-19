/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_finset_dirichlet_sum_eq_and_independent_of_gammaH (git blob ba69b1570c9422203ce238a016c55edfdc3f27c1, sha256 adeefeb34702cbb242d0f6edb8694fd2e340038d54aab157af7dd26f79d22031).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_finset_dirichlet_sum_eq_and_independent_of_gammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_finset_dirichlet_sum_eq_and_independent_of_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    (∀ f : CuspForm (CohCarrier.GammaH M H) k,
      ∃ (s : Finset (DirichletCharacter ℂ M)) (fε : DirichletCharacter ℂ M → CuspForm (CohCarrier.GammaH M H) k),
        (∀ ε ∈ s, ∀ d : (ZMod M)ˣ, d ∈ H → ε (d : ZMod M) = 1) ∧
        (∀ ε ∈ s, ∀ σ : CongruenceSubgroup.Gamma0 M,
          ⇑(fε ε) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
            ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • ⇑(fε ε)) ∧
        ⇑f = ∑ ε ∈ s, ⇑(fε ε)) ∧
    (∀ (s : Finset (DirichletCharacter ℂ M)) (g : DirichletCharacter ℂ M → CuspForm (CohCarrier.GammaH M H) k),
      (∀ ε ∈ s, ∀ σ : CongruenceSubgroup.Gamma0 M,
          ⇑(g ε) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
            ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • ⇑(g ε)) →
      (∑ ε ∈ s, ⇑(g ε)) = 0 → ∀ ε ∈ s, g ε = 0) := by
  revert M H k
  exact @_root_.P2MW.S_CuspForm_exists_finset_dirichlet_sum_eq_and_independent_of_gammaH.solution
