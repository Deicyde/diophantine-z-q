import ZInQKernel.Contrib.RLeaf.IgusaX0
import ZInQKernel.Contrib.CloudB2X0Transitive.Bridge

/-!
# `ZInQ.RLeaf.X0Transitive` from the cyclic-quotient bijection (a reduction, not a proof)

`ZInQ.RLeaf.X0Transitive` (`ZInQKernel/Contrib/RLeaf/IgusaX0.lean:69`, unchanged) is derived here
from one hypothesis, `CyclicQuotientJBijOn` (`Bridge.lean`): the exact statement, at universe
`0`, of Anthropic FLT's
`WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j`
(anthropics/fermats-last-theorem, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, Apache-2.0).
The rest of the argument (irreducibility of `Φ_N(X, j)` over `ℚ(j)`, existence of the modular
polynomial data, Galois equivariance of `C ↦ j(E/C)`, normality of `\overline{ℚ(j)}/ℚ(j)`) is
proved: Mathlib and the ported FLT theorems under `Vendor/AnthropicFLT/`.

This module imports both the target's own closure (with Tau Ceti's elliptic-curve modules) and the
ported FLT cone, so it also witnesses that the two coexist in one environment.

No `sorry`, no `axiom`, no `native_decide`. **`X0Transitive` itself is not proved here**: the
proof cone of the FLT bijection (661 modules) does not port to Lean 4.35 / Mathlib `56a00585`
without wide changes, and three of its files declare names that Tau Ceti also declares.
-/

namespace ZInQ.Contrib.CloudB2X0Transitive

/-- **`X₀(N)`-transitivity from the cyclic-quotient bijection** (reduction): with
`CyclicQuotientJBijOn`, the Galois group of `\overline{ℚ(j)}/ℚ(j)` permutes the cyclic subgroups of
order `N` of `E_j` transitively, for every `N > 0`. -/
theorem x0Transitive_of_cyclicQuotientJBijOn (hB : CyclicQuotientJBijOn) :
    ZInQ.RLeaf.X0Transitive :=
  fun N P P' hN hP hP' => x0Transitive_unfolded_of_bijOn hB N P P' hN hP hP'

end ZInQ.Contrib.CloudB2X0Transitive
