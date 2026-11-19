import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.Glue
import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-!
# GenusOdd: vocabulary for the local form of `ArtinFactorization`

Definitions only (no claims):

* `localPolyK E 𝔭`: Mathlib's local polynomial of `E/K` at a prime `𝔭` of `K` (minimal model of
  `E` over the completion `K_𝔭`), the polynomial whose inverse is the Euler factor used in CST's
  `twistedLFunction`;
* `localPolyQ E v`: Mathlib's local polynomial of `E/ℚ` at a place `v` of `ℚ` (the one in
  `E.LFunction`);
* `primesAbove K p`: the finite set of primes `𝔭` of `K` with `p ∈ 𝔭`;
* `UnramifiedOver 𝔭 p`: `𝔭² ∤ p 𝓞_K` (ramification index one);
* `GoodAt E v`: the minimal model of `E` over `ℚ_v` has good reduction (as in the twist
  dictionary of `RC/TwistDictionary`).
-/

noncomputable section

open NumberField IsDedekindDomain

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

/-- Mathlib's local polynomial of `E/K` at the prime `𝔭` of `K`: computed from a minimal model of
`E` over the completion `K_𝔭`; `1 − a T + N𝔭 T²` (good), `1 − T` / `1 + T` (split / nonsplit
multiplicative), `1` (additive). Its inverse, at `T = N𝔭^{-s}` and rescaled by `χ(𝔭)`, is the Euler
factor of CST's `twistedLFunction`. -/
def localPolyK (E : WeierstrassCurve ℚ) {K : Type} [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (𝓞 K)) : Polynomial ℤ :=
  ((E.baseChange K).baseChange (𝔭.adicCompletion K)).localPolynomial (𝔭.adicCompletionIntegers K)

/-- Mathlib's local polynomial of `E/ℚ` at the place `v` of `ℚ` (the factor of `E.LFunction`). -/
def localPolyQ (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : Polynomial ℤ :=
  (E.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ)

/-- The primes of `K` above the rational prime `p`: the maximal ideals `𝔭` with `p ∈ 𝔭` (a finite
set: the prime factors of `p 𝓞_K`). -/
def primesAbove (K : Type) [Field K] [NumberField K] (p : ℕ) : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔭 | ((p : ℤ) : 𝓞 K) ∈ 𝔭.asIdeal}

/-- `𝔭` is unramified over `p`: `𝔭² ∤ p 𝓞_K` (ramification index one). -/
def UnramifiedOver {K : Type} [Field K] [NumberField K] (𝔭 : HeightOneSpectrum (𝓞 K)) (p : ℕ) :
    Prop :=
  ¬ 𝔭.asIdeal ^ 2 ∣ Ideal.span {((p : ℤ) : 𝓞 K)}

/-- `E` has good reduction at the place `v` of `ℚ`: the minimal model of `E` over `ℚ_v` has good
reduction (the hypothesis of `twistDictionary_of_good`). -/
def GoodAt (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  ((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).HasGoodReduction
    (v.adicCompletionIntegers ℚ)

end ZInQ.Contrib.CloudB3RC53.GenusOdd
