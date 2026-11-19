/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_heckeTLinOne_slashOfMemGamma0 (git blob f1a80076a09d06a3ddef364752bfd8a4eca2799d, sha256 89168b3fcf11b23c20bb74ff8c21b9e248c823e54fab2a77b1bc7b2cbe50decb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_Gamma1HeckeOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspForm_heckeTLinOne_slashOfMemGamma0

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem solution
    {M : ℕ} (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (f : CuspForm (Gamma1 M) k) :
    CuspForm.heckeTLinOne k hℓ hℓM (CuspForm.slashOfMemGamma0 M k hγ f) =
      CuspForm.slashOfMemGamma0 M k hγ (CuspForm.heckeTLinOne k hℓ hℓM f) := by
  obtain ⟨σ, hσ⟩ := CuspForm.exists_isDiamondLift_of_coprime (M := M)
    ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM)
  refine DFunLike.ext' ?_
  rw [CuspForm.coe_heckeTLinOne_apply_of_isDiamondLift k hℓ hℓM hσ, CuspForm.coe_slashOfMemGamma0,
    CuspForm.coe_slashOfMemGamma0, CuspForm.coe_heckeTLinOne_apply_of_isDiamondLift k hℓ hℓM hσ]
  exact (CuspForm.Gamma1Hecke.heckeU_add_slash_heckeDiagMatrix_slash_of_mem_Gamma0 k hℓ hℓM
    (fun g hg => SlashInvariantFormClass.slash_action_eq f g hg) σ hσ.1 hσ.2 hγ).symm
