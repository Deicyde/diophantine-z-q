/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus (git blob 89f8a794e4579a9e43ecf095146d17908fd62582, sha256 71ca001d0b2c7a990b9baa0db89a384570efba54ab422143a9d22b3a0df7a01a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (ε : DirichletCharacter ℂ M)
    (f : CuspForm (CohCarrier.GammaH M H) k) (g : CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hfg : (⇑f : UpperHalfPlane → ℂ) = ⇑g) (hg : CuspForm.HasNebentypus ε g) :
    (∀ d : (ZMod M)ˣ, (⇑(CuspForm.diamondLinH k d f) : UpperHalfPlane → ℂ) = ε (d : ZMod M) • ⇑g) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      (⇑(CuspForm.heckeTLinH k hℓ hℓM f) : UpperHalfPlane → ℂ) =
        ModularForm.heckeU k ℓ ⇑g + ε (ℓ : ZMod M) • ((⇑g) ∣[k] ModularForm.heckeDiagMatrix ℓ)) ∧
    (∀ (q : ℕ), q.Prime → q ∣ M →
      (⇑(CuspForm.heckeULinH k q f) : UpperHalfPlane → ℂ) = ModularForm.heckeU k q ⇑g) := by
  revert M H k ε f g hfg hg
  exact @_root_.P2MW.S_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus.solution
