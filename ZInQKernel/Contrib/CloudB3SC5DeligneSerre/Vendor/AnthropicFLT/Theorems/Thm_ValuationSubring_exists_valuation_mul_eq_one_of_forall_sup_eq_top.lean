/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_exists_valuation_mul_eq_one_of_forall_sup_eq_top (git blob c6d2382496643f75aa7ff423cf0ccee35a1836e8, sha256 af11710a989dadf5f7d53e0165ed95c90934111063497e4981fccbc7b894d7f1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_valuation_mul_eq_one_of_forall_sup_eq_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.exists_valuation_mul_eq_one_of_forall_sup_eq_top
    {F F' : Type*} [Field F] [Field F'] [Algebra F F'] [FiniteDimensional F F']
    (Q : ValuationSubring F) (S : Finset (ValuationSubring F'))
    (hS : ∀ P ∈ S, P.comap (algebraMap F F') = Q)
    {σ : Type*} [Fintype σ] (cls : σ → ValuationSubring F') (hcls : ∀ s, cls s ∈ S)
    (ω : σ → F') (hω : ∀ s, ω s ∈ cls s)
    (hind : ∀ P ∈ S, ∀ a : σ → F, (∀ s, a s ∈ Q) → (∀ s, cls s ≠ P → a s = 0) →
      (∃ s, Q.valuation (a s) = 1) → P.valuation (∑ s, algebraMap F F' (a s) * ω s) = 1)
    (hcard : Module.finrank F F' ≤ Fintype.card σ)
    (P₀ : ValuationSubring F') (hP₀ : P₀ ∈ S) (hindep : ∀ P ∈ S, P ≠ P₀ → P₀ ⊔ P = ⊤)
    (g : F') (hg : g ≠ 0) :
    ∃ h : F, P₀.valuation (algebraMap F F' h * g) = 1 := by
  revert F F' Q S hS σ cls hcls ω hω hind hcard P₀ hP₀ hindep g hg
  exact @_root_.P2MW.S_ValuationSubring_exists_valuation_mul_eq_one_of_forall_sup_eq_top.solution
