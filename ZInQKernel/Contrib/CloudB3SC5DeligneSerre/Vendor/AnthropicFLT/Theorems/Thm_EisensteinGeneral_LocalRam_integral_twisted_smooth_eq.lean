/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq (git blob 0338d2a802117e53e90efcc95a127b613456d25f, sha256 31e5015be408f5765d143f19fb71869736434a74e9c585a5e661a78a0f20f599).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField

theorem EisensteinGeneral.LocalRam.integral_twisted_smooth_eq
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (ϖ : (v.adicCompletion F)ˣ) (hϖ : Valued.v (ϖ : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (v.adicCompletion F)ˣ →* ℂˣ)
    (c : ℕ) (hc : 1 ≤ c) (hχ : ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt F v c, χ u = 1)
    (m : ℕ) (hm : 1 ≤ m)
    (A : v.adicCompletion F → ℂ)
    (hA : IntegrableOn A (v.adicCompletionIntegers F : Set (v.adicCompletion F)) μ)
    (B : v.adicCompletion F → ℂ)
    (hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x)
    (s : ℂ) (hs : ‖((χ ϖ : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s))‖ < 1)
    (ψ : AddChar (v.adicCompletion F) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion F, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (ξ : v.adicCompletion F) (e : ℤ) (hξ : Valued.v ξ = WithZero.exp e) :
    ∫ x, (((v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
          + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
              (fun y => LanglandsTunnell.TateLocal.charExt χ⁻¹ y
                * ((LanglandsTunnell.TateLocal.modulus y : ℝ) : ℂ) ^ (-(2 * s + 1)) * B y⁻¹) x)
          * ψ (-(ξ * x))) ∂μ
      = (∫ x in (v.adicCompletionIntegers F : Set (v.adicCompletion F)), A x * ψ (-(ξ * x)) ∂μ)
        + ∑ k ∈ Finset.Icc 1 (max ((m : ℤ) - 1) (n + (c : ℤ) - e)).toNat,
            (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(2 * s + 1))) ^ k
              * ∫ x in {x : v.adicCompletion F | Valued.v x = WithZero.exp (k : ℤ)},
                  LanglandsTunnell.TateLocal.charExt χ⁻¹ x * B x⁻¹ * ψ (-(ξ * x)) ∂μ := by
  revert F v μ ϖ hϖ χ c hc hχ m hm A hA B hB s hs ψ n hψn hψn' ξ e hξ
  exact @_root_.P2MW.S_EisensteinGeneral_LocalRam_integral_twisted_smooth_eq.solution
