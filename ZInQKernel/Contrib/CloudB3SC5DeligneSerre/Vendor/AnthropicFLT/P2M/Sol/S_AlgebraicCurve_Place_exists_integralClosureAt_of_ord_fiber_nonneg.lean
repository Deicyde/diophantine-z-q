/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg (git blob 6c966c6b986ac8326ac10d6902ee1e52d8ee7e19, sha256 35dc29141f41c215099cf893022dbb053a7a2b2e409d744444c60c443061d938).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOverDVR
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_count_normalizedFactors_span_singleton

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_exists_integralClosureAt_of_ord_fiber_nonneg

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid AlgebraicCurve AlgebraicCurve.Place

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0)
    (hord : ∀ w ∈ v.fiber F', 0 ≤ w.ord f) :
    ∃ c : integralClosureAt F' v, algebraMap (integralClosureAt F' v) F' c = f := by
  classical

  obtain ⟨⟨c₀, s₀⟩, hcs⟩ := IsLocalization.surj
    (nonZeroDivisors (integralClosureAt F' v)) f
  have hs0 : (s₀ : integralClosureAt F' v) ≠ 0 := nonZeroDivisors.coe_ne_zero s₀
  have hsF : algebraMap (integralClosureAt F' v) F' (s₀ : integralClosureAt F' v) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mpr hs0
  have hcF : algebraMap (integralClosureAt F' v) F' c₀ ≠ 0 := by
    rw [← hcs]; exact mul_ne_zero hf hsF
  have hc0 : c₀ ≠ 0 := fun h => hcF (by rw [h, map_zero])

  have hdom : ∀ (w : Place K F') (hw : w.restrict F = v),
      w.ord (algebraMap (integralClosureAt F' v) F' (s₀ : integralClosureAt F' v))
        ≤ w.ord (algebraMap (integralClosureAt F' v) F' c₀) := by
    intro w hw
    have h1 : w.ord (algebraMap (integralClosureAt F' v) F' c₀)
        = w.ord f + w.ord (algebraMap (integralClosureAt F' v) F' (s₀ :
            integralClosureAt F' v)) := by
      rw [← hcs]; exact w.ord_mul hf hsF
    have h2 := hord w (mem_fiber.mpr hw)
    omega

  have hle : Ideal.span {c₀} ≤ Ideal.span {(s₀ : integralClosureAt F' v)} := by
    have hspan_c : (Ideal.span {c₀} : Ideal (integralClosureAt F' v)) ≠ ⊥ := fun h =>
      hc0 (Ideal.span_singleton_eq_bot.mp h)
    have hspan_s : (Ideal.span {(s₀ : integralClosureAt F' v)} :
        Ideal (integralClosureAt F' v)) ≠ ⊥ := fun h => hs0 (Ideal.span_singleton_eq_bot.mp h)
    rw [← Ideal.dvd_iff_le, dvd_iff_normalizedFactors_le_normalizedFactors hspan_s hspan_c,
      Multiset.le_iff_count]
    intro P
    by_cases hP : P ∈ normalizedFactors
      (Ideal.span {(s₀ : integralClosureAt F' v)} : Ideal (integralClosureAt F' v))
    ·
      have hPprime : Prime P := prime_of_normalized_factor P hP
      haveI : P.IsPrime := Ideal.isPrime_of_prime hPprime
      have hres := restrict_placeOfPrime
        (⟨P, inferInstance, hPprime.ne_zero⟩ : HeightOneSpectrum (integralClosureAt F' v))
      have hPeq : (fiberCenter F' v hres).asIdeal = P := congrArg HeightOneSpectrum.asIdeal
        (fiberCenter_placeOfPrime
          (⟨P, inferInstance, hPprime.ne_zero⟩ : HeightOneSpectrum (integralClosureAt F' v)))
      rw [← hPeq, AlgebraicCurve.Place.count_normalizedFactors_span_singleton hres hs0,
        AlgebraicCurve.Place.count_normalizedFactors_span_singleton hres hc0]
      exact Int.toNat_le_toNat (hdom _ hres)
    · rw [Multiset.count_eq_zero_of_notMem hP]
      exact Nat.zero_le _

  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (hle (Ideal.mem_span_singleton_self c₀))
  refine ⟨d, ?_⟩
  have hmapped := congrArg (algebraMap (integralClosureAt F' v) F') hd
  rw [map_mul] at hmapped
  refine mul_left_cancel₀ hsF ?_
  rw [← hmapped, ← hcs]
  ring
