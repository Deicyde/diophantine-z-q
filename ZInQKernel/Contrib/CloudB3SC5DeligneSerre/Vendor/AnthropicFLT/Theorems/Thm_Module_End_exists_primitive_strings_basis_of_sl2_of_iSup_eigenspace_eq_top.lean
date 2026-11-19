/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Module_End_exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top (git blob 26a5f6b5037c2e1f976dd99fbe3319e07e6a58f3, sha256 2ee35cd10c2e6a5e23b7f7fde35887baee817ace55d931b5e51fa9c73aa041a2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Complex.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Module_End_exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem Module.End.exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (e f h : V →ₗ[ℂ] V)
    (hhe : h ∘ₗ e - e ∘ₗ h = (2 : ℂ) • e) (hhf : h ∘ₗ f - f ∘ₗ h = -((2 : ℂ) • f)) (hef : e ∘ₗ f - f ∘ₗ e = h)
    (hdiag : ⨆ μ : ℂ, Module.End.eigenspace h μ = ⊤) :
    ∃ (r : ℕ) (t : Fin r → V) (n : Fin r → ℕ),
      (∀ i, e (t i) = 0 ∧ h (t i) = (n i : ℂ) • t i ∧ (f ^ (n i + 1)) (t i) = 0) ∧
      (∀ i (p : ℕ), p ≤ n i →
        h ((f ^ p) (t i)) = ((n i : ℂ) - 2 * (p : ℂ)) • (f ^ p) (t i) ∧
        e ((f ^ (p + 1)) (t i)) = (((p : ℂ) + 1) * ((n i : ℂ) - (p : ℂ))) • (f ^ p) (t i)) ∧
      LinearIndependent ℂ (fun x : (Σ i : Fin r, Fin (n i + 1)) => (f ^ (x.2 : ℕ)) (t x.1)) ∧
      Submodule.span ℂ (Set.range (fun x : (Σ i : Fin r, Fin (n i + 1)) => (f ^ (x.2 : ℕ)) (t x.1))) = ⊤ := by
  revert V e f h hhe hhf hef hdiag
  exact @_root_.P2MW.S_Module_End_exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top.solution
