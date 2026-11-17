/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply (git blob c7944b6ab95a52b7636ed064d41ce72092729a29, sha256 408daa24c4ba5d69470535aa07a098d5d2843fcf091c289f9378a63c773ad819).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    ∃ (n : ℕ) (L : Fin n → ℕ) (hL : ∀ i, L i ∣ M)
      (ε : (i : Fin n) → DirichletCharacter ℂ (L i))
      (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
      (G : Fin n → ℕ → CuspForm (CohCarrier.GammaH M H) k),
      (∀ i, CuspForm.IsPrimitiveForm (ε i) (g i)) ∧
      (∀ i j, i ≠ j → L i ≠ L j ∨ ∃ m : ℕ, ModularFormClass.qCoeff (g i) m ≠ ModularFormClass.qCoeff (g j) m) ∧
      (∀ i, ∀ u : (ZMod M)ˣ, u ∈ H → DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) = 1) ∧
      (∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        ∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ)) ∧
      LinearIndependent ℂ (fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) ∧
      Submodule.span ℂ (Set.range fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) = ⊤ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (i : Fin n) (d : ℕ), d ∣ M / L i →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CuspForm.heckeTLinH k hℓ hℓM (G i d) = ModularFormClass.qCoeff (g i) ℓ • G i d) ∧
      (∀ (u : (ZMod M)ˣ) (i : Fin n) (d : ℕ), d ∣ M / L i →
        CuspForm.diamondLinH k u (G i d) = DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) • G i d) ∧
      (∀ (q : ℕ), q.Prime → q ∣ M → ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        (q ∣ d → CuspForm.heckeULinH k q (G i d) = G i (d / q)) ∧
        (¬ q ∣ d → q ∣ L i → CuspForm.heckeULinH k q (G i d) = ModularFormClass.qCoeff (g i) q • G i d) ∧
        (¬ q ∣ d → ¬ q ∣ L i → CuspForm.heckeULinH k q (G i d) =
          ModularFormClass.qCoeff (g i) q • G i d - (ε i (q : ZMod (L i)) * (q : ℂ) ^ (k - 1)) • G i (d * q))) := by
  revert M H k
  exact @_root_.P2MW.S_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply.solution
