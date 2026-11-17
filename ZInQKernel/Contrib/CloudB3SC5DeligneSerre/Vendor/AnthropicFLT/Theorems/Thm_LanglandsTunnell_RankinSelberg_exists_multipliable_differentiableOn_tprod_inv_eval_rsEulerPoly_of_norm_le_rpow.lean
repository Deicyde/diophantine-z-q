/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow (git blob a70791e4371a7b3ac9162c81e02828708c132d6e, sha256 06e2eebd46756b0b06f8c75164ce4960092a703a73b46f1c1f9fc501c04e7159).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_RankinSelberg_exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open _root_.IsDedekindDomain
open _root_.NumberField hiding multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one

theorem LanglandsTunnell.RankinSelberg.exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow
    (K : Type) [Field K] [NumberField K] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a b a' b' : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} → ℂ) (κ : ℝ)
    (hbd : ∀ v, ‖a v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖b v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧
      ‖a' v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ ∧ ‖b' v‖ ≤ ((Ideal.absNorm v.1.asIdeal : ℕ) : ℝ) ^ κ) :
    ∃ σ₀ : ℝ,
      (∀ s : ℂ, σ₀ < s.re →
        Multipliable (fun v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S} =>
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹)) ∧
      DifferentiableOn ℂ (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) {s : ℂ | σ₀ < s.re} ∧
      (∀ s : ℂ, σ₀ < s.re →
        (∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
          ((LanglandsTunnell.RankinSelberg.rsEulerPoly (a v) (b v) (a' v) (b' v) 0).eval
            (((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹) ≠ 0) := by
  revert K S a b a' b' κ hbd
  exact @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_exists_multipliable_differentiableOn_tprod_inv_eval_rsEulerPoly_of_norm_le_rpow.solution
