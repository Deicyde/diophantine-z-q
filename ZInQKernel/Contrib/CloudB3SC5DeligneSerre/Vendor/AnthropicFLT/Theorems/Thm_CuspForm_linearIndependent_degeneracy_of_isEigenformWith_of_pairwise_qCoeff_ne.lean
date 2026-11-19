/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspForm_linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne (git blob 4f874b87c4e6611daabfbbf124776e060a27c3c7, sha256 2f53efef74ccfd55ebe7f089fb4e184dc9a72f6ecc5fae77ade14b90df140d43).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspForm_linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspForm.linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne
    (M : ℕ) [NeZero M] (k : ℤ) (n : ℕ) (L : Fin n → ℕ) [∀ i, NeZero (L i)] (hL : ∀ i, L i ∣ M)
    (ε : (i : Fin n) → DirichletCharacter ℂ (L i))
    (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
    (hg : ∀ i, CuspForm.IsEigenformWith (ε i) (g i))
    (hsep : ∀ i j : Fin n, i ≠ j → ∃ p : ℕ, p.Prime ∧ ¬ p ∣ M ∧
      ModularFormClass.qCoeff (g i) p ≠ ModularFormClass.qCoeff (g j) p)
    (G : Fin n → ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hG : ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
      ∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ))
    (c : Fin n → ℕ → ℂ)
    (hc : (∑ i, ∑ d ∈ Nat.divisors (M / L i), c i d • G i d) = 0) :
    ∀ (i : Fin n), ∀ d ∈ Nat.divisors (M / L i), c i d = 0 := by
  revert M k n L hL ε g hg hsep G hG c hc
  exact @_root_.P2MW.S_CuspForm_linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne.solution
