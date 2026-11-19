/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_gamma1_frickeRational_sigmaTransport (git blob 5103756ab660ddeeb535a318dd8b1a63d91da878, sha256 bf42d7ad11dfc56dbde0f80df5cd5662c560e735fca74b2680fc6d2165a6ce5b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_gamma1_frickeRational_sigmaTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Manifold
end Manifold
namespace MatrixGroups
end MatrixGroups
namespace ModularForm
end ModularForm

set_option autoImplicit false
open Complex Real UpperHalfPlane
open _root_.Manifold
open _root_.MatrixGroups
open _root_.ModularForm hiding exists_mul_E4_pow_mul_E6_pow_eq_iff

theorem ModularForm.exists_gamma1_frickeRational_sigmaTransport
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (K : IntermediateField ℚ ℂ)
    (hK : K = IntermediateField.adjoin ℚ
      {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))})
    (s : ℕ) (hs : Nat.Coprime s N)
    (φ : ↥K →+* ℂ)
    (hφ : ∀ z : ↥K, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (f : ModularForm (CongruenceSubgroup.Gamma1 N) k)
    (P Q : MvPolynomial (Option {v : Fin 2 → ZMod N // v ≠ 0}) ↥K)
    (hQ0 : MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
      o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) ≠ 0)
    (hid : ∀ τ : ℍ, f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) (Q.map (algebraMap ↥K ℂ)) τ =
      ModularForm.discriminant τ ^ m *
        MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
          o.elim jf fun v => fricke v.1) (P.map (algebraMap ↥K ℂ)) τ) :
    ∃ f' : ModularForm (CongruenceSubgroup.Gamma1 N) k,
      MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
        o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) ≠ 0 ∧
      ∀ τ : ℍ, f' τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) *
          MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
            o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (Q.map φ) τ =
        ModularForm.discriminant τ ^ m *
          MvPolynomial.aeval (fun o : Option {v : Fin 2 → ZMod N // v ≠ 0} =>
            o.elim jf fun v => fricke ![v.1 0, (s : ZMod N) * v.1 1]) (P.map φ) τ := by
  revert N L hL W hW fricke hfricke jf hjf K hK s hs φ hφ k a b m hk f P Q hQ0 hid
  exact @_root_.P2MW.S_ModularForm_exists_gamma1_frickeRational_sigmaTransport.solution
