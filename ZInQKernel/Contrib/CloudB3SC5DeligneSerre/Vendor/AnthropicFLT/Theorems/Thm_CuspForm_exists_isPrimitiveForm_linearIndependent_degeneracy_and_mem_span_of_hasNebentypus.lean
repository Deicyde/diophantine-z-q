/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus (git blob da208f0c60bed885fe34fedc5b67b7d032c78d47, sha256 a3c08b4df463222059549df2ee1dc3cc84c1f58d5869119e20c9228eb5631197).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) :
    ∃ (n : ℕ) (L : Fin n → ℕ) (hL : ∀ i, L i ∣ M)
      (εL : (i : Fin n) → DirichletCharacter ℂ (L i))
      (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
      (G : Fin n → ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k),
      (∀ i, CuspForm.IsPrimitiveForm (εL i) (g i)) ∧
      (∀ i j, i ≠ j → L i ≠ L j ∨ ∃ m : ℕ, ModularFormClass.qCoeff (g i) m ≠ ModularFormClass.qCoeff (g j) m) ∧
      (∀ i, DirichletCharacter.changeLevel (hL i) (εL i) = ε) ∧
      (∀ (L' : ℕ) [NeZero L'] (hL' : L' ∣ M) (ε' : DirichletCharacter ℂ L')
          (g' : CuspForm (CongruenceSubgroup.Gamma1 L') k),
        CuspForm.IsPrimitiveForm ε' g' → DirichletCharacter.changeLevel hL' ε' = ε →
        ∃ i, L i = L' ∧ ∀ m : ℕ, ModularFormClass.qCoeff (g i) m = ModularFormClass.qCoeff g' m) ∧
      (∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        (∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ)) ∧
        CuspForm.HasNebentypus ε (G i d)) ∧
      LinearIndependent ℂ (fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) ∧
      (∀ f : CuspForm (CongruenceSubgroup.Gamma1 M) k, CuspForm.HasNebentypus ε f →
        f ∈ Submodule.span ℂ (Set.range fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ))) := by
  revert M k ε
  exact @_root_.P2MW.S_CuspForm_exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus.solution
