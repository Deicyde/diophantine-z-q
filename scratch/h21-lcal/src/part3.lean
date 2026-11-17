
/-! # h21-lcal, part 3: TYZ's `𝓛(n)²` as printed, and `h21C`/`h21S` restated with it

TYZ (arXiv:1411.4728v1, L338–353, as transcribed by the project: `scratch/rv-tyz-inputs/tyzcalc.py`,
`docs/research/h33-sign.md`, `rv-tyz-inputs.md` §1.7; the source is not on this host) define `𝓛(n)` for odd
squarefree `n` by cases on `r = ord_{s=1} L(E_n, s)`: `𝓛(n) = 0` if `r > 1`; `𝓛(n)² = L(E_n, 1)/(2^{2k−2−a}Ω_n)`
if `r = 0`; `𝓛(n)² = L′(E_n, 1)/(2^{2k−2−a}Ω_n R_n)` if `r = 1` (`R_n` the regulator), with `a = 1` for odd `n`.
The project's `lcalSq m = L(C_m, 1)/(2^{2k−3}Ω_m)` is the `r = 0` branch; it agrees with the printed
definition on the classes `1, 3 (mod 8)` because `r ≠ 1` there (`analyticOrderAt_ne_one`, root number `+1`),
and when `r ≥ 2` both are `0`. -/

namespace ZInQ.Contrib.H21Lcal

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp
open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.TYZDecomp.H29Genus NumberField
open ZInQ.Contrib.T21Proof ZInQ.Contrib.HfxProof ZInQ.Contrib.TYZGenusFold ZInQ.Contrib.H21CSteps
open scoped Quaternion

open Classical in
/-- **TYZ's `𝓛(n)²` as printed (L338–353), odd `n`**, for a given regulator function `R` (`R n` stands for TYZ's
`R_n`, twice the Néron–Tate height of a generator of `E_n(ℚ)/E_n(ℚ)_tors` in rank one; it enters only the
branch `ord = 1`, which never occurs on the classes `1, 3 (mod 8)`, so the value there does not depend on `R`:
`lcalSqPrinted_eq`). `F` is the entire continuation of Mathlib's `L(C_n, s)` (`C_n ≅ E_n : ny² = x³ − x` over
`ℚ`), unique by `IsLContinuation.eq`; `k = #{p ∣ n}`, `a = 1`; `Ω_n = omegaTYZ n = (2/√n)∫₁^∞ dx/√(x³ − x)`.
Junk `0` if there is no continuation (there always is: `ZInQ.Contrib.heckeContinuation`). -/
noncomputable def lcalSqPrinted (R : ℕ → ℝ) (n : ℕ) : ℂ :=
  if h : ∃ F : ℂ → ℂ, IsLContinuation (ZInQ.Contrib.TYZDecomp.curveC n) F then
    if analyticOrderAt h.choose 1 = 0 then
      h.choose 1 / ((2 : ℂ) ^ ((2 * n.primeFactors.card : ℤ) - 3) * (omegaTYZ n : ℂ))
    else if analyticOrderAt h.choose 1 = 1 then
      deriv h.choose 1 /
        ((2 : ℂ) ^ ((2 * n.primeFactors.card : ℤ) - 3) * (omegaTYZ n : ℂ) * (R n : ℂ))
    else 0
  else 0

set_option linter.deprecated false in
/-- **Step (a) of the queue10 verdict on `h21C`**: on squarefree `m ≡ 1, 3 (mod 8)`, the project's `lcalSq m`
is TYZ's printed `𝓛(m)²`, for every regulator function `R`. -/
theorem lcalSqPrinted_eq (R : ℕ → ℝ) {m : ℕ} (hsq : Squarefree m) (hcl : m % 8 = 1 ∨ m % 8 = 3) :
    lcalSqPrinted R m = lcalSq m := by
  have hex : ∃ F : ℂ → ℂ, IsLContinuation (ZInQ.Contrib.TYZDecomp.curveC m) F :=
    ZInQ.Contrib.heckeContinuation m hsq.ne_zero
  have hF := hex.choose_spec
  have hL : lValOne m = hex.choose 1 := lValOne_eq hF
  have h1 := analyticOrderAt_ne_one hcl hsq hF
  rw [lcalSqPrinted, dif_pos hex, lcalSq, hL]
  by_cases h0 : analyticOrderAt hex.choose 1 = 0
  · rw [if_pos h0]
  · rw [if_neg h0, if_neg h1]
    have hz : hex.choose 1 = 0 := by
      by_contra hne
      exact h0 (analyticOrderAt_eq_zero.mpr (Or.inr hne))
    rw [hz, zero_div]

/-- `ℓ` is a complex sign choice of TYZ's printed `𝓛` on the squarefree classes `1, 3 (mod 8)`. -/
def IsLcalSignPrinted (R : ℕ → ℝ) (ℓ : ℕ → ℂ) : Prop :=
  ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ℓ m ^ 2 = lcalSqPrinted R m

theorem isLcalSignPrinted_iff (R : ℕ → ℝ) (ℓ : ℕ → ℂ) : IsLcalSignPrinted R ℓ ↔ IsLcalSignC ℓ :=
  ⟨fun h m hsq hcl => (h m hsq hcl).trans (lcalSqPrinted_eq R hsq hcl),
   fun h m hsq hcl => (h m hsq hcl).trans (lcalSqPrinted_eq R hsq hcl).symm⟩

/-- **TYZ Theorem 2.1 (L554–559) with TYZ's printed `𝓛` (L338–353)**: `TYZThm21PairsC` (tyz-genus) with the
sign choices `ℓ(m)² = 𝓛(m)²` taken against `lcalSqPrinted R` (the case split on `ord_{s=1}` as printed) for every
regulator function `R`, instead of the project's `lcalSq`. Same restrictions as `TYZThm21PairsC` (odd classes,
`n > 1`, the first assertion only for pairs with no factor `≡ 1 (mod 8)`). Equivalent to `TYZThm21PairsC`
(`tyzThm21PairsC_of_printed`, `tyzThm21PairsPrinted_of_C`), and to its instance at any single `R`. -/
def TYZThm21PairsPrinted : Prop :=
  ∀ R : ℕ → ℝ, ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVector n τ f →
      ∀ ℓ : ℕ → ℂ, IsLcalSignPrinted R ℓ → ∀ d₁ d₂ : ℕ, d₁ * d₂ = n →
        (d₁ % 8 ≠ 1 → d₂ % 8 ≠ 1 → quadPeriod n τ f d₂ = 0) ∧
        (d₂ % 8 = 1 → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          (quadPeriod n τ f d₂ : ℂ) = ε * 2 ^ (n.primeFactors.card - 1) *
            ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℂ) * (ℓ d₁ * ℓ d₂))

theorem tyzThm21PairsC_of_printed (h : TYZThm21PairsPrinted) : TYZThm21PairsC := by
  intro n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  exact h (fun _ => 0) n hsq h1 hcl τ hτ f hf ℓ ((isLcalSignPrinted_iff _ ℓ).mpr hℓ) d₁ d₂ hd

theorem tyzThm21PairsPrinted_of_C (h : TYZThm21PairsC) : TYZThm21PairsPrinted := by
  intro R n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  exact h n hsq h1 hcl τ hτ f hf ℓ ((isLcalSignPrinted_iff R ℓ).mp hℓ) d₁ d₂ hd

/-- **TYZ Theorem 2.1 with `π^U` of Theorem 2.4(1) (h21c-steps' `TYZThm21Span`) and TYZ's printed `𝓛`**:
`TYZThm21Span` with `lcalSqPrinted R` for every `R` in place of `lcalSq`. Equivalent to `TYZThm21Span`
(`tyzThm21Span_of_printed`, `tyzThm21SpanPrinted_of_span`), hence to `TYZThm21PairsC`. -/
def TYZThm21SpanPrinted : Prop :=
  ∀ R : ℕ → ℝ, ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVectorSpan n τ f →
      ∀ ℓ : ℕ → ℂ, IsLcalSignPrinted R ℓ → ∀ d₁ d₂ : ℕ, d₁ * d₂ = n →
        (d₁ % 8 ≠ 1 → d₂ % 8 ≠ 1 → quadPeriod n τ f d₂ = 0) ∧
        (d₂ % 8 = 1 → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          (quadPeriod n τ f d₂ : ℂ) = ε * 2 ^ (n.primeFactors.card - 1) *
            ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℂ) * (ℓ d₁ * ℓ d₂))

theorem tyzThm21Span_of_printed (h : TYZThm21SpanPrinted) : TYZThm21Span := by
  intro n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  exact h (fun _ => 0) n hsq h1 hcl τ hτ f hf ℓ ((isLcalSignPrinted_iff _ ℓ).mpr hℓ) d₁ d₂ hd

theorem tyzThm21SpanPrinted_of_span (h : TYZThm21Span) : TYZThm21SpanPrinted := by
  intro R n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  exact h n hsq h1 hcl τ hτ f hf ℓ ((isLcalSignPrinted_iff R ℓ).mp hℓ) d₁ d₂ hd

/-- `h21C` from the printed span form (the fold used on `frozenTarget`). -/
theorem tyzThm21PairsC_of_spanPrinted (h : TYZThm21SpanPrinted) : TYZThm21PairsC :=
  tyzThm21PairsC_of_span (tyzThm21Span_of_printed h)

/-- **Non-vacuity of the printed definition**: `𝓛(1)² = 1` (TYZ L1082), from lcal-one's proof of `TYZLcalOne`
through `lcalSqPrinted_eq`; so `IsLcalSignPrinted R ℓ` forces `ℓ 1 = ±1`. -/
theorem lcalSqPrinted_one (R : ℕ → ℝ) : lcalSqPrinted R 1 = 1 :=
  (lcalSqPrinted_eq R squarefree_one (Or.inl rfl)).trans ZInQ.Contrib.LcalOne.tyzLcalOne_proof

end ZInQ.Contrib.H21Lcal
