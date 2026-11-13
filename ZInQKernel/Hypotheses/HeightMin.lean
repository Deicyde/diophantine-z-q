import ZInQKernel.Multiplication.Certificate.Constants

/-!
# Hypothesis H, in the one instance the proof uses

The six-contact estimate `SixContactEstimate` (Theorem 4.1) quantifies over every admissible
prime set `S` and parameter `R`. The proof of Theorem 1.1 uses it twice, at `S = S_ht`, `R = D`
(the precision bound of the value relation) and at `S = S_mul`, `R = max(D, H_max, c_*, 10¹²)`
(the finite box of multiplication soundness). Both uses follow from the single instance

  `h(u) ≤ H₆(D) · M_{S_mul}(u)²⁴` for every `u ∈ ℚ \ 𝒞`,

because `M_{S_mul}(u) ∣ M_{S_ht}(u)` (`S_ht ⊆ S_mul`), `H₆(D) = A⁽⁰⁾_ht` and `H₆` is monotone in
`R`. This file states that instance as `SixContactMin` and derives the precision use
(`Compiler.Precision.sixContact_at_heightPrimes`); the multiplication use is
`Mult.sixContact_at_Smul`. That `SixContactEstimate` implies `SixContactMin` is
`sixContactMin_of_sixContactEstimate` (`ZInQKernel/Main.lean`): the instance `R = D` is admissible
for `S_mul` because `H_max, c_* < D`, a consequence of the catalogue bound `catalogueBound8`.

The constant is written `heightH6 heightD`, in the vocabulary of `Hypotheses/Height.lean`, so
that `SixContactMin` is visibly the instance `S = S_mul`, `R = D` of `SixContactEstimate`; it
equals the precision constant `A⁽⁰⁾_ht` (`Compiler.Precision.A0_eq_heightH6`). The prime set is
named: `Mult.S_mul = S_ht ∪ 𝓗 ∪ supp(c_*)`, with `S_ht` the primes `≤ 324`, `𝓗` the
catalogue of twenty-two primes above `324` in each unit class modulo `W = 4·324#`, and
`c_* = 4 M₀` with `M₀` the least formal multiple of `N_s`; its defining expression is not
readable inline.

## Trust

`SixContactMin` is not proved in Lean. It is the instance `S = S_mul`, `R = D` of
`SixContactEstimate`, and `sixContactMin_of_sixContactEstimate` (`ZInQKernel/Main.lean`) derives
it in Lean. Its justification is therefore exactly that of Theorem 4.1, recorded in the module
docstring of `Hypotheses/Height.lean` and in `docs/research/h-trust.md`. The instance is
admissible because `S_mul` consists of primes, contains the primes `≤ 324`, `max S_mul ≤ D`, and
`10¹² ≤ D`; the proof of Theorem 4.1 uses `R` only through these lower bounds. H cannot be
narrowed further or removed (`docs/research/h-map.md` §§1, 3.1, 3.3): the two consumers need a
bound that is effective and uniform in `u`.
-/

namespace ZInQ

open scoped BigOperators

/-- **Hypothesis H, minimal form.** For every `u ∈ ℚ \ 𝒞`, `h(u) ≤ H₆(D) · M_{S_mul}(u)²⁴`, where
`H₆(D) = A⁽⁰⁾_ht = 2·10¹³ max(1, C_cm, (D^(D E₀))¹⁷)`. This is the instance `S = S_mul`, `R = D`
of the six-contact estimate `SixContactEstimate`. It is the only form of H that the main theorems
assume. Its trust statement is that of Theorem 4.1: refereed theorems plus model-reviewed
arguments, with no unpublished upstream proof supplement (`Hypotheses/Height.lean`,
`docs/research/h-trust.md`). -/
def SixContactMin : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ratHeight u ≤ heightH6 (heightD : ℝ) * (contactSupport Mult.S_mul u : ℝ) ^ 24

theorem heightH6_nonneg (R : ℝ) : 0 ≤ heightH6 R := by
  unfold heightH6; positivity

/-- `H₆` is monotone in `R` on `[1, ∞)`. -/
theorem heightH6_mono_of_one_le {R R' : ℝ} (h1 : 1 ≤ R) (h : R ≤ R') :
    heightH6 R ≤ heightH6 R' := by
  have hE : (0 : ℝ) ≤ heightE0 := Nat.cast_nonneg _
  have hq : heightQ R ≤ heightQ R' := by
    unfold heightQ
    calc R ^ (R * heightE0) ≤ R' ^ (R * heightE0) :=
          Real.rpow_le_rpow (by linarith) h (mul_nonneg (by linarith) hE)
      _ ≤ R' ^ (R' * heightE0) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (mul_le_mul_of_nonneg_right h hE)
  have hq0 : 0 ≤ heightQ R := Real.rpow_nonneg (by linarith) _
  unfold heightH6
  gcongr

/-- `M_S(u) > 0`: a product of primes. -/
theorem contactSupport_pos (S : Finset ℕ) (u : ℚ) : 0 < contactSupport S u := by
  unfold contactSupport
  exact Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

/-- `M_{S'}(u) ∣ M_S(u)` for `S ⊆ S'`: a prime counted for `S'` is counted for `S`. -/
theorem contactSupport_dvd_of_subset {S S' : Finset ℕ} (h : S ⊆ S') (u : ℚ) :
    contactSupport S' u ∣ contactSupport S u := by
  unfold contactSupport
  refine Finset.prod_dvd_prod_of_subset _ _ _ fun p hp => ?_
  rw [Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, fun hS => hp.2.1 (h hS), hp.2.2⟩

theorem Mult.heightPrimes_subset_S_mul : Compiler.Precision.heightPrimes ⊆ Mult.S_mul :=
  fun _ hp => Mult.mem_S_mul.2 (Or.inl hp)

/-- **The six-contact estimate at `S = S_ht`, `R = D`:** `h(u) ≤ A⁽⁰⁾_ht M_{S_ht}(u)²⁴`, from
`SixContactMin` since `M_{S_mul}(u) ≤ M_{S_ht}(u)`. -/
theorem Compiler.Precision.sixContact_at_heightPrimes (hH : SixContactMin) {u : ℚ}
    (hu : u ∉ contactSet) :
    ratHeight u ≤ (Compiler.Precision.A0 : ℝ) * (contactSupport heightPrimes u : ℝ) ^ 24 := by
  rewrite [Compiler.Precision.A0_eq_heightH6]
  refine (hH u hu).trans (mul_le_mul_of_nonneg_left ?_ (heightH6_nonneg _))
  have hle : contactSupport Mult.S_mul u ≤ contactSupport heightPrimes u :=
    Nat.le_of_dvd (contactSupport_pos _ _)
      (contactSupport_dvd_of_subset Mult.heightPrimes_subset_S_mul u)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hle) 24

end ZInQ
