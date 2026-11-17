/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AutomorphicForm_archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul (git blob 2d389ad577122af6e05d1c729a6ff56dfdfd986e, sha256 1ecc4eb04d071f54c5e6948b6cdc812ae826596e7dd1ad95937f5cd9d5f8b532).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AutomorphicForm_archDelAt_E_archDelAt_Fm_add_archDelBarAt_Fm_archDelBarAt_E_eq_of_archDerivAtComplex_iH_eq_smul

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem solution
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchSmoothAtComplex hw φ) (m : ℂ)
    (hm : archDerivAtComplex hw .iH φ = m • φ) :
    -(archDelAt hw .E (archDelAt hw .Fm φ) + archDelBarAt hw .Fm (archDelBarAt hw .E φ))
      = archCasimirAtComplex hw φ + archCasimirBarAtComplex hw φ
        + (1 / 8 : ℂ) • archDerivAtComplex hw .H (archDerivAtComplex hw .H φ)
        - (m ^ 2 / 8 - Complex.I * m / 2) • φ := by
  obtain ⟨-, -, hEF, -, -, hEiF, hiEF, -, -, -, -, hiEiF, -, -, -⟩ :=
    archDerivAtComplex_commutator_of_isArchSmoothAtComplex F hw φ hφ
  have hs : ∀ d : ArchDirComplex, IsArchSmoothAtComplex hw (archDerivAtComplex hw d φ) :=
    fun d => hφ.archDerivAtComplex d
  have linSub : ∀ (X : ArchDirComplex) (u v : AdelicGL2 (𝓞 F) F → ℂ),
      IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v → ∀ (a c : ℂ),
      archDerivAtComplex hw X (a • (u - c • v)) = a • (archDerivAtComplex hw X u - c • archDerivAtComplex hw X v) := by
    intro X u v hu hv a c
    rw [archDerivAtComplex_smul, sub_eq_add_neg, ← neg_smul, archDerivAtComplex_add hu (hv.smul _),
      archDerivAtComplex_smul, neg_smul, ← sub_eq_add_neg]
  have linAdd : ∀ (X : ArchDirComplex) (u v : AdelicGL2 (𝓞 F) F → ℂ),
      IsArchSmoothAtComplex hw u → IsArchSmoothAtComplex hw v → ∀ (a c : ℂ),
      archDerivAtComplex hw X (a • (u + c • v)) = a • (archDerivAtComplex hw X u + c • archDerivAtComplex hw X v) := by
    intro X u v hu hv a c
    rw [archDerivAtComplex_smul, archDerivAtComplex_add hu (hv.smul _), archDerivAtComplex_smul]
  simp only [archDelAt, archDelBarAt, archCasimirAtComplex, archCasimirBarAtComplex, ArchDir.toComplex,
    ArchDir.toComplexI, linSub _ _ _ (hs _) (hs _), linAdd _ _ _ (hs _) (hs _)]
  have hHH : archDerivAtComplex hw .iH (archDerivAtComplex hw .iH φ) = m • (m • φ) := by
    rw [hm, archDerivAtComplex_smul, hm]
  rw [hHH]
  rw [hm] at hEiF hiEF
  rw [hm]
  funext g
  have h3 := congrFun hEF g
  have h6 := congrFun hEiF g
  have h7 := congrFun hiEF g
  have h12 := congrFun hiEiF g
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h3 h6 h7 h12 ⊢
  linear_combination (1 / 4 : ℂ) * h3 + (Complex.I / 4) * h6 + (Complex.I / 4) * h7 - (1 / 4 : ℂ) * h12
    + ((1 / 4 : ℂ) * (archDerivAtComplex hw .iE (archDerivAtComplex hw .iFm φ) g
        - archDerivAtComplex hw .iFm (archDerivAtComplex hw .iE φ) g) + m ^ 2 * φ g / 8) * Complex.I_sq
