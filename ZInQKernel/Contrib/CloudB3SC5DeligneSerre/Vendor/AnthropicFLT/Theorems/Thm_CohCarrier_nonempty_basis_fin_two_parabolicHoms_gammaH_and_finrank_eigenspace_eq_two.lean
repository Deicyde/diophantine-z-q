/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CohCarrier_nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two (git blob 0e1957bf36073162857d52b9ceeead02afbad64e, sha256 6649af44f3b7ec53cefb42b650dfe76c3a8e57c6e1b3a0a77f2fb08b33c4e422).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Inst
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodMap
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Analysis.Complex.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CohCarrier_nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem CohCarrier.nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (hSfin : S.Finite) :
    Nonempty (Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℂ {T : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) |
            (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), (ℓ ∉ S ∨ ℓ ∣ M) ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ)) ∨
            (∃ d : (ZMod M)ˣ, ∀ v,
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.diamondL M H ℂ d (v : CohCarrier.H1 M H ℂ))})
      ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) ∧
    ∀ χ : ↥(Algebra.adjoin ℂ {T : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) |
            (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), (ℓ ∉ S ∨ ℓ ∣ M) ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ)) ∨
            (∃ d : (ZMod M)ˣ, ∀ v,
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.diamondL M H ℂ d (v : CohCarrier.H1 M H ℂ))}) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ {T : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ) |
            (∃ (ℓ : ℕ) (hℓ : ℓ.Prime), (ℓ ∉ S ∨ ℓ ∣ M) ∧ ∀ v, haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.heckeT M H ℓ ℂ (v : CohCarrier.H1 M H ℂ)) ∨
            (∃ d : (ZMod M)ˣ, ∀ v,
              ((T v : ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) :
                CohCarrier.H1 M H ℂ) = CohCarrier.diamondL M H ℂ d (v : CohCarrier.H1 M H ℂ))}),
        Module.End.eigenspace (a : Module.End ℂ
          ↥(ModularCurve.Period.parabolicHoms ℂ (CohCarrier.GammaH M H) ℂ)) (χ a)) = 2 := by
  revert M H S hSfin
  exact @_root_.P2MW.S_CohCarrier_nonempty_basis_fin_two_parabolicHoms_gammaH_and_finrank_eigenspace_eq_two.solution
