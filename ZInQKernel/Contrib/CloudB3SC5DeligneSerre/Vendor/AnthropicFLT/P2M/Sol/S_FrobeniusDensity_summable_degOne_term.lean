/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_FrobeniusDensity_summable_degOne_term (git blob 76b55e6372d32c8f51873c5ec47c8aba8d859bcd, sha256 dfe4fae9f5387e098062002e760db7d52eb6107187e5775b4bf3f727e86f0e8e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_FrobeniusDensity_idealSum_ne_top
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_FrobeniusDensity_primeSum_eq_degOneSum_add
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FrobeniusDensity_PrimeSums

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace Ideal
end Ideal
namespace NumberField
end NumberField
namespace IsDedekindDomain
end IsDedekindDomain
namespace Ideal.IsDedekindDomain
end Ideal.IsDedekindDomain
namespace FrobeniusDensity
end FrobeniusDensity
namespace P2MW.S_FrobeniusDensity_summable_degOne_term.FrobeniusDensity
end P2MW.S_FrobeniusDensity_summable_degOne_term.FrobeniusDensity

namespace P2MW.S_FrobeniusDensity_summable_degOne_term

set_option autoImplicit false

open _root_.Ideal
open _root_.NumberField
open _root_.IsDedekindDomain
open _root_.Ideal.IsDedekindDomain
open scoped ENNReal

namespace FrobeniusDensity
export _root_.FrobeniusDensity (idealSum_ne_top normRpow idealSum primeSum degOneSum degOneCount primeSum_eq_degOneSum_add)
open _root_.FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

private lemma primeSum_le_idealSum (s : ℝ) : primeSum K s ≤ idealSum K s := by
  have hinj : Function.Injective
      (fun v : HeightOneSpectrum (𝓞 K) =>
        (⟨v.asIdeal, v.ne_bot⟩ : {I : Ideal (𝓞 K) // I ≠ ⊥})) :=
    fun v w h => HeightOneSpectrum.ext (by simpa using congrArg Subtype.val h)
  exact ENNReal.tsum_comp_le_tsum_of_injective hinj fun I => normRpow K s I.1

private lemma degOneSum_ne_top (S₀ : Finset ℕ) {s : ℝ} (hs : 1 < s) : degOneSum K S₀ s ≠ ⊤ := by
  have h1 : degOneSum K S₀ s ≤ primeSum K s := by
    rw [primeSum_eq_degOneSum_add K S₀ s, add_assoc]
    exact self_le_add_right _ _
  exact (h1.trans_lt ((primeSum_le_idealSum K s).trans_lt
    (idealSum_ne_top K hs).lt_top)).ne

omit [NumberField K] in
private theorem toReal_term (S₀ : Finset ℕ) (s : ℝ) (ℓ : ℕ) :
    ((if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ≥0∞)) * (ℓ : ℝ≥0∞) ^ (-s)).toReal
      = (if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s) := by
  rw [ENNReal.toReal_mul, apply_ite ENNReal.toReal, ENNReal.toReal_zero,
    ENNReal.toReal_natCast, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast]

end FrobeniusDensity

open _root_.FrobeniusDensity
open _root_.P2MW.S_FrobeniusDensity_summable_degOne_term.FrobeniusDensity

theorem solution (K : Type*) [Field K] [NumberField K] (S₀ : Finset ℕ) {s : ℝ} (hs : 1 < s) :
    Summable (fun ℓ : ℕ => (if ℓ ∈ S₀ then 0 else
      (FrobeniusDensity.degOneCount K ℓ : ℝ)) * (ℓ : ℝ) ^ (-s)) :=
  (ENNReal.summable_toReal (degOneSum_ne_top K S₀ hs)).congr (toReal_term K S₀ s)
