import ZInQKernel.Contrib.OneProof.TYZThm21GChar
import ZInQKernel.Contrib.OneProof.H21Lcal

/-!
# h21-combine: TYZ Theorem 2.1 with TYZ's genus character and TYZ's printed `𝓛²`

Task h21-combine; report `docs/research/h21-combine.md`, log `scratch/h21-combine/log.md`. TYZ = Tian–Yuan–Zhang,
*Genus periods, genus points and congruent number problem*, Asian J. Math. 21 (2017), arXiv:1411.4728v1; line numbers
`Lnnnn` refer to the arXiv source (not on this host; they are the project's transcriptions, UNVERIFIED here).

The queue10 verdict on `h21C` named three composite steps between the Lean statement and TYZ's print:
(a) the project's `lcalSq` against TYZ's printed `𝓛²` (L338–353), (b) the Legendre-symbol character `gchar` against
TYZ's genus character `χ_{d₁,d₂}`, (c) `InPiZ` against TYZ's `π_ℤ^{U_n}`. h21c-steps read (c) through Theorem 2.4(1)
(`H21CSteps.TYZThm21Span`, `h21S`). h21-lcal proved (a) (`H21Lcal.lcalSqPrinted_eq`, from root number `+1`), giving
`H21Lcal.TYZThm21SpanPrinted`; h21-gchar proved (b) (`H21GChar.tyzChiCl_eq_gchar`), giving
`H21GChar.TYZThm21SpanG`. This file states one hypothesis with both:

* `TYZThm21SpanGP`: `h21S` with the quadratic period formed with TYZ's character (`H21GChar.quadPeriodTYZ`) and the
  sign choices taken against TYZ's printed `𝓛²` for every regulator function (`H21Lcal.IsLcalSignPrinted R`);
* `tyzThm21Span_of_GP`, `tyzThm21SpanGP_of_span`: it is equivalent to `h21S` (the two dictionaries compose);
* `tyzThm21PairsC_of_GP`: the form `OneProof.Main` reads (`h21C`).

No `sorry`, no `axiom`.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.H21Combine

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp
open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.TYZDecomp.H29Genus NumberField
open ZInQ.Contrib.T21Proof ZInQ.Contrib.HfxProof ZInQ.Contrib.TYZGenusFold ZInQ.Contrib.H21CSteps
open ZInQ.Contrib.H21GChar ZInQ.Contrib.H21Lcal
open scoped Quaternion

/-- **TYZ Theorem 2.1 (L554–559) with TYZ's genus character and TYZ's printed `𝓛`**: for every regulator function
`R` (TYZ's `R_n`, read only in the branch `ord_{s=1} = 1` of `𝓛`, which does not occur here), every squarefree
`1 < n ≡ 1, 3 (mod 8)`, every admissible embedding `τ` (L527–534), every test vector `f_n` (a `ℤ`-generator of
`π_ℤ^{U_n}` with `π^U = ⊕_δ ℂ f_δ` as printed in Theorem 2.4(1), L615–623, `IsTestVectorSpan`), every complex sign
choice `ℓ` of TYZ's printed `𝓛` (`ℓ(m)² = 𝓛(m)²` with `𝓛²` split on `ord_{s=1} L(E_m, s)` as at L338–353,
`IsLcalSignPrinted R`) and every `n = d₁d₂`: the quadratic period `P(d₁, d₂) = Σ_{t ∈ Cl_n} χ_{d₁,d₂}(t) f_n(t)`
(L551–552) formed with TYZ's `χ_{d₁,d₂}`, the character of `Cl_n = Gal(H_n/K_n)` attached to `K_n(√d₂*)` through the
Artin map (`quadPeriodTYZ`), vanishes when neither factor is `≡ 1 (mod 8)`, and for `d₂ ≡ 1 (mod 8)`,
`P(d₁, d₂) = ±2^{k−a} w_K 𝓛(d₁)𝓛(d₂)` (`k − a = #{p ∣ n} − 1`, `2w_K` the number of roots of unity of `K_n`).
Word for word `H21CSteps.TYZThm21Span` with `quadPeriod` replaced by `quadPeriodTYZ` (h21-gchar's
`TYZThm21SpanG`) and `IsLcalSignC` by `IsLcalSignPrinted R` for every `R` (h21-lcal's `TYZThm21SpanPrinted`). Same
restrictions as `TYZThm21Span` (odd classes, `n > 1`, the first assertion only for pairs with no factor
`≡ 1 (mod 8)`). -/
def TYZThm21SpanGP : Prop :=
  ∀ R : ℕ → ℝ, ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVectorSpan n τ f →
      ∀ ℓ : ℕ → ℂ, IsLcalSignPrinted R ℓ → ∀ d₁ d₂ : ℕ, d₁ * d₂ = n →
        (d₁ % 8 ≠ 1 → d₂ % 8 ≠ 1 → quadPeriodTYZ n τ f d₂ = 0) ∧
        (d₂ % 8 = 1 → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          (quadPeriodTYZ n τ f d₂ : ℂ) = ε * 2 ^ (n.primeFactors.card - 1) *
            ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℂ) * (ℓ d₁ * ℓ d₂))

/-- Step (a) (h21-lcal): the printed `𝓛²` gives h21-gchar's `TYZThm21SpanG`. -/
theorem tyzThm21SpanG_of_GP (h : TYZThm21SpanGP) : TYZThm21SpanG := by
  intro n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  exact h (fun _ => 0) n hsq h1 hcl τ hτ f hf ℓ ((isLcalSignPrinted_iff _ ℓ).mpr hℓ) d₁ d₂ hd

/-- The converse of `tyzThm21SpanG_of_GP`. -/
theorem tyzThm21SpanGP_of_G (h : TYZThm21SpanG) : TYZThm21SpanGP := by
  intro R n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  exact h n hsq h1 hcl τ hτ f hf ℓ ((isLcalSignPrinted_iff R ℓ).mp hℓ) d₁ d₂ hd

/-- **`h21S` from the combined statement** (steps (a) and (b): h21-lcal's and h21-gchar's dictionaries). -/
theorem tyzThm21Span_of_GP (h : TYZThm21SpanGP) : TYZThm21Span :=
  tyzThm21Span_of_G (tyzThm21SpanG_of_GP h)

/-- The converse: `TYZThm21SpanGP ↔ TYZThm21Span`. -/
theorem tyzThm21SpanGP_of_span (h : TYZThm21Span) : TYZThm21SpanGP :=
  tyzThm21SpanGP_of_G (tyzThm21SpanG_of_span h)

theorem tyzThm21SpanGP_iff_span : TYZThm21SpanGP ↔ TYZThm21Span :=
  ⟨tyzThm21Span_of_GP, tyzThm21SpanGP_of_span⟩

/-- The combined statement is also equivalent to h21-lcal's `TYZThm21SpanPrinted`. -/
theorem tyzThm21SpanGP_iff_printed : TYZThm21SpanGP ↔ TYZThm21SpanPrinted :=
  tyzThm21SpanGP_iff_span.trans
    ⟨tyzThm21SpanPrinted_of_span, tyzThm21Span_of_printed⟩

/-- **`h21C` from the combined statement**: the form `OneProof.Main` reads (twice). -/
theorem tyzThm21PairsC_of_GP (h : TYZThm21SpanGP) : TYZThm21PairsC :=
  tyzThm21PairsC_of_span (tyzThm21Span_of_GP h)

/-- Non-vacuity of the sign premise: for every `R` there is a complex sign choice of TYZ's printed `𝓛`. -/
theorem exists_isLcalSignPrinted (R : ℕ → ℝ) : ∃ ℓ : ℕ → ℂ, IsLcalSignPrinted R ℓ :=
  ⟨fun m => lcalSqPrinted R m ^ (((2 : ℕ) : ℂ)⁻¹), fun m _ _ =>
    Complex.cpow_nat_inv_pow (lcalSqPrinted R m) two_ne_zero⟩

end ZInQ.Contrib.H21Combine

#print axioms ZInQ.Contrib.H21Combine.tyzThm21Span_of_GP
#print axioms ZInQ.Contrib.H21Combine.tyzThm21SpanGP_of_span
#print axioms ZInQ.Contrib.H21Combine.tyzThm21SpanGP_iff_printed
#print axioms ZInQ.Contrib.H21Combine.tyzThm21PairsC_of_GP
#print axioms ZInQ.Contrib.H21Combine.exists_isLcalSignPrinted
