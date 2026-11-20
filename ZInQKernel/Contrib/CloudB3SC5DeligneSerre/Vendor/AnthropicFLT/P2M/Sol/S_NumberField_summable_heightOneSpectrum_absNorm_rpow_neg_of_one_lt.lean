/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt (git blob 5b7a07343005e65c502f06285bb4c6164740a14f, sha256 fecd17c36118a70a0a905ca4599ec8f7315ee2d46fc1bbf3a3ecafa2e5ba1830).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.Analysis.PSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_summable_heightOneSpectrum_absNorm_rpow_neg_of_one_lt

set_option autoImplicit false

open NumberField IsDedekindDomain

-- [port] Mathlib 4.35 `Ideal.absNorm` needs `Infinite (𝓞 F)` (a characteristic-zero ring is infinite)
local instance (F : Type) [Field F] [NumberField F] : Infinite (𝓞 F) :=
  Infinite.of_injective (Nat.cast : ℕ → 𝓞 F) Nat.cast_injective

theorem solution
    (F : Type) [Field F] [NumberField F] {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) := by
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ p n : ℕ, 0 < n ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal ∧
      p.Prime ∧ Ideal.absNorm v.asIdeal = p ^ n := fun v => by
    haveI : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
    exact Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
  choose p n hn hmem hp hN using hex
  have hterm : ∀ v : HeightOneSpectrum (𝓞 F),
      ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ) ≤ ((p v : ℕ) : ℝ) ^ (-σ) := by
    intro v
    refine Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (hp v).pos) ?_ (by linarith)
    rw [hN v]
    exact_mod_cast Nat.le_self_pow (hn v).ne' (p v)
  have hfib : ∀ (T : Finset (HeightOneSpectrum (𝓞 F))) (v₀ : HeightOneSpectrum (𝓞 F)),
      (T.filter fun v => p v = p v₀).card ≤ Module.finrank ℚ F := by
    intro T v₀
    have hqZ : Prime ((p v₀ : ℕ) : ℤ) := Nat.prime_iff_prime_int.mp (hp v₀)
    have hq0 : Ideal.span {((p v₀ : ℕ) : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact hqZ.ne_zero
    haveI hqmax : (Ideal.span {((p v₀ : ℕ) : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime hqZ.ne_zero).mpr hqZ).isMaximal hq0
    refine (Finset.card_le_card_of_injOn HeightOneSpectrum.asIdeal ?_ ?_).trans
      (Ideal.card_primesOverFinset_le_finrank (S := 𝓞 F) ℚ F hq0)
    · intro v hv
      have hv' : (p v : ℕ) = p v₀ := (Finset.mem_filter.mp hv).2
      rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hq0]
      refine ⟨v.isPrime, ⟨?_⟩⟩
      refine hqmax.eq_of_le (Ideal.comap_ne_top _ v.isPrime.ne_top) ?_
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast, ← hv']
      exact hmem v
    · intro v₁ _ v₂ _ h
      exact HeightOneSpectrum.ext h
  have hnat : Summable fun m : ℕ => (m : ℝ) ^ (-σ) := Real.summable_nat_rpow.mpr (by linarith)
  refine summable_of_sum_le (c := (Module.finrank ℚ F : ℝ) * ∑' m : ℕ, (m : ℝ) ^ (-σ))
    (fun v => by positivity) (fun T => ?_)
  calc ∑ v ∈ T, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-σ)
      ≤ ∑ v ∈ T, ((p v : ℕ) : ℝ) ^ (-σ) := Finset.sum_le_sum fun v _ => hterm v
    _ = ∑ q ∈ T.image p, ∑ v ∈ T.filter (fun v => p v = q), ((p v : ℕ) : ℝ) ^ (-σ) :=
        (Finset.sum_fiberwise_of_maps_to (fun v hv => Finset.mem_image_of_mem p hv) _).symm
    _ ≤ ∑ q ∈ T.image p, (Module.finrank ℚ F : ℝ) * (q : ℝ) ^ (-σ) := by
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨v₀, -, rfl⟩ := Finset.mem_image.mp hq
        calc ∑ v ∈ T.filter (fun v => p v = p v₀), ((p v : ℕ) : ℝ) ^ (-σ)
            = ∑ v ∈ T.filter (fun v => p v = p v₀), ((p v₀ : ℕ) : ℝ) ^ (-σ) := by
              refine Finset.sum_congr rfl fun v hv => ?_
              rw [(Finset.mem_filter.mp hv).2]
          _ = ((T.filter fun v => p v = p v₀).card : ℝ) * ((p v₀ : ℕ) : ℝ) ^ (-σ) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ (Module.finrank ℚ F : ℝ) * ((p v₀ : ℕ) : ℝ) ^ (-σ) := by
              gcongr
              exact hfib T v₀
    _ = (Module.finrank ℚ F : ℝ) * ∑ q ∈ T.image p, (q : ℝ) ^ (-σ) := by rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ F : ℝ) * ∑' m : ℕ, (m : ℝ) ^ (-σ) := by
        gcongr
        exact hnat.sum_le_tsum _ (fun m _ => by positivity)
