/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm (git blob 55b1d19a29d9950d97f733a4948d6dcf733f288e, sha256 a565bb6b0f140454107c47b8c33fb9e7afc7937bc6d4f29acb3158786a54cda4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    (∀ (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓ' : ℓ'.Prime) (hℓ'M : ¬ ℓ' ∣ M)
        (f : CuspForm (CohCarrier.GammaH M H) k),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      haveI : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
      CuspForm.heckeTLinH k hℓ hℓM (CuspForm.heckeTLinH k hℓ' hℓ'M f) =
        CuspForm.heckeTLinH k hℓ' hℓ'M (CuspForm.heckeTLinH k hℓ hℓM f)) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (q : ℕ), q.Prime → q ∣ M →
        ∀ f : CuspForm (CohCarrier.GammaH M H) k,
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CuspForm.heckeTLinH k hℓ hℓM (CuspForm.heckeULinH k q f) =
        CuspForm.heckeULinH k q (CuspForm.heckeTLinH k hℓ hℓM f)) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CuspForm.heckeTLinH k hℓ hℓM (CuspForm.diamondLinH k d f) =
        CuspForm.diamondLinH k d (CuspForm.heckeTLinH k hℓ hℓM f)) ∧
    (∀ (q : ℕ), q.Prime → q ∣ M → ∀ (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k),
      CuspForm.heckeULinH k q (CuspForm.diamondLinH k d f) =
        CuspForm.diamondLinH k d (CuspForm.heckeULinH k q f)) ∧
    (∀ (d d' : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k),
      CuspForm.diamondLinH k d (CuspForm.diamondLinH k d' f) =
        CuspForm.diamondLinH k d' (CuspForm.diamondLinH k d f)) := by
  revert M H k
  exact @_root_.P2MW.S_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm.solution
