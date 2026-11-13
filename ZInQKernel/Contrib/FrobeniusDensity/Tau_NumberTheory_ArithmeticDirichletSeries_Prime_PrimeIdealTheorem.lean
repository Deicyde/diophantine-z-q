/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Ported for the T18 contribution from TauCetiProject/TauCeti@1f9b4414105d86e487a4ac4c3d3397076a44d0d2,
TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/PrimeIdealTheorem.lean. Changes: imports relocated to the owned flat contribution directory;
proof and definition bodies initially unchanged. Project pins are not changed.
See docs/research/t18-frobenius-density.md for attribution and license text.
-/
module

public import ZInQKernel.Contrib.FrobeniusDensity.Tau_NumberTheory_LFunctions_PrimeIdealBoundary

/-!
# The prime ideal theorem

The analytic boundary data of the Dedekind zeta function supplies the generic prime-number-theorem
transfer with residue one. This gives asymptotics for the three standard counting functions of
prime ideals in a number field: Chebyshev's `ψ` and `ϑ`, and the unweighted count `π`.

## Main results

* `TauCeti.primeIdealTheorem`: `ψ_K(x) ~ x`, `ϑ_K(x) ~ x`, and `π_K(x) ~ Li(x)`.
* `TauCeti.primeCount_univ_isEquivalent_div_log`: the classical form `π_K(x) ~ x / log x`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
* H. Davenport, *Multiplicative Number Theory*, Chapter 17.
-/

public section

namespace TauCeti

open NumberField Asymptotics Filter

variable (K : Type*) [Field K] [NumberField K]

/-- **The prime ideal theorem.** For a number field `K`, Chebyshev's functions satisfy
`ψ_K(x) ~ x` and `ϑ_K(x) ~ x`, and the number `π_K(x)` of prime ideals of norm at most `x`
satisfies `π_K(x) ~ Li(x)`. -/
theorem primeIdealTheorem :
    primePsi K Set.univ ~[atTop] (fun x : ℝ ↦ x) ∧
      primeTheta K Set.univ ~[atTop] (fun x : ℝ ↦ x) ∧
      primeCount K Set.univ ~[atTop] Real.logIntegral :=
  primeIdealTheorem_of_boundary (LFunctions.primeIdealVonMangoldtBoundary K)

/-- **The prime ideal theorem, in the form `π_K(x) ~ x / log x`.** -/
theorem primeCount_univ_isEquivalent_div_log :
    primeCount K Set.univ ~[atTop] fun x : ℝ ↦ x / Real.log x :=
  (primeIdealTheorem K).2.2.trans Real.logIntegral_isEquivalent_div_log

end TauCeti
