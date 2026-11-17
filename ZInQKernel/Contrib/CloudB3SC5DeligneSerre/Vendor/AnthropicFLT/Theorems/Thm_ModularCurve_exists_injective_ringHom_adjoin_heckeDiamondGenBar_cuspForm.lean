/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm (git blob d91e3e3551332cd3873200d7baf6ae6fd1ab615e, sha256 fd6fa2676874b30daa08a50de84c83a4c9afa498eaaae617a0b33aafdad9d42c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_Gamma1HeckeOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm (M : ℕ) [NeZero M]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M) :
    ∃ Φ : ↥(Algebra.adjoin ℤ (Set.range (ModularCurve.heckeDiamondGenBar M))) →+*
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) 2),
      Function.Injective Φ ∧
      (∀ (ℓ : Nat.Primes) (hℓM : ¬ (ℓ : ℕ) ∣ M),
        Φ ⟨ModularCurve.heckeOperatorOneBar M ℓ,
            Algebra.subset_adjoin (Set.mem_range_self (Sum.inl ℓ))⟩
          = CuspForm.heckeTLinOne 2 ℓ.prop hℓM) ∧
      ∀ (d : ℕ), Nat.Coprime d M →
        Φ ⟨ModularCurve.diamondOneBar M d,
            Algebra.subset_adjoin (Set.mem_range_self (Sum.inr d))⟩
          = CuspForm.diamondLinOne M 2 d := by
  revert M hin hcomm
  exact @_root_.P2MW.S_ModularCurve_exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm.solution
