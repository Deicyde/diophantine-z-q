/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one (git blob 50a5611b94e9fb0c099b5a5a627eb59d6a032624, sha256 8516bb17db33cc81d70fee1f53569345c9be8b1731826ac4031c532b4526aea8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Basis.Defs
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem CuspForm.nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ) (hSfin : S.Finite) :
    Nonempty (Module.Basis (Fin 1)
      ↥(Algebra.adjoin ℂ {T : Module.End ℂ (CuspForm (CohCarrier.GammaH M H) 2) |
          (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ∉ S ∧ T = CuspForm.heckeTLinH 2 hℓ hℓM) ∨
          (∃ q : ℕ, q.Prime ∧ q ∣ M ∧ T = CuspForm.heckeULinH 2 q) ∨
          (∃ d : (ZMod M)ˣ, T = CuspForm.diamondLinH 2 d)})
      (CuspForm (CohCarrier.GammaH M H) 2)) ∧
    ∀ χ : ↥(Algebra.adjoin ℂ {T : Module.End ℂ (CuspForm (CohCarrier.GammaH M H) 2) |
          (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ∉ S ∧ T = CuspForm.heckeTLinH 2 hℓ hℓM) ∨
          (∃ q : ℕ, q.Prime ∧ q ∣ M ∧ T = CuspForm.heckeULinH 2 q) ∨
          (∃ d : (ZMod M)ˣ, T = CuspForm.diamondLinH 2 d)}) →ₐ[ℂ] ℂ,
      Module.finrank ℂ ↥(⨅ a : ↥(Algebra.adjoin ℂ {T : Module.End ℂ (CuspForm (CohCarrier.GammaH M H) 2) |
          (∃ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M), ℓ ∉ S ∧ T = CuspForm.heckeTLinH 2 hℓ hℓM) ∨
          (∃ q : ℕ, q.Prime ∧ q ∣ M ∧ T = CuspForm.heckeULinH 2 q) ∨
          (∃ d : (ZMod M)ˣ, T = CuspForm.diamondLinH 2 d)}),
        Module.End.eigenspace (a : Module.End ℂ (CuspForm (CohCarrier.GammaH M H) 2)) (χ a)) = 1 := by
  revert M H S hSfin
  exact @_root_.P2MW.S_CuspForm_nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one.solution
