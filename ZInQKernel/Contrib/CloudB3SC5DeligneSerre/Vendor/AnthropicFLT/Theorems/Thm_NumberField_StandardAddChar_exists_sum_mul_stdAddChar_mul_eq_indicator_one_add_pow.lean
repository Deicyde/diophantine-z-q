/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_StandardAddChar_exists_sum_mul_stdAddChar_mul_eq_indicator_one_add_pow (git blob 7fe2c1a26a66ee703402b4ab022a61a868720b02, sha256 5d52e1c254192d4979419432d2005bf88cc46f98a7ab7b3ca3bf8076075cd425).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_StandardAddChar_exists_sum_mul_stdAddChar_mul_eq_indicator_one_add_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.StandardAddChar.exists_sum_mul_stdAddChar_mul_eq_indicator_one_add_pow
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (m n : ℕ) (hn : 0 < n) :
    ∃ (r : ℕ) (y : Fin r → AdeleRing (𝓞 K) K) (c : Fin r → ℂ),
      (∀ i, (y i).1 = 0 ∧ ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v → (y i).2 v' = 0) ∧
      ∀ a : AdeleRing (𝓞 K) K,
        Valued.v (a.2 v) ≤ ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
        (∑ i, c i * NumberField.StandardAddChar.stdAddChar K (a * y i)) =
          if Valued.v (a.2 v - 1) ≤
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
          then 1 else 0 := by
  revert K v m n hn
  exact @_root_.P2MW.S_NumberField_StandardAddChar_exists_sum_mul_stdAddChar_mul_eq_indicator_one_add_pow.solution
