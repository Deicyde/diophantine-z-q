import ZInQKernel.Hypotheses.PrimePattern
import ZInQKernel.Multiplication.Certificate.Constants

/-!
# Hypothesis 22P_AP: long arithmetic progressions of good slope primes

Route AP of `docs/research/nt-22p.md` (§3.3–3.4). This replaces the prime-pattern hypothesis
22P (`FixedPrimePattern`) and the two-slope pattern 22P₂ (`TwoSlopePattern`) in the main
theorem (`exists_bounded_integer_polynomial_defining_integers_of_goodPrimeAP`); the polynomial
is unchanged. The statement mentions neither the integer `A`, nor the catalogue multipliers,
nor valuations at the old primes: only the lower bound `max S_b` for the primes.
-/

namespace ZInQ

/-- **Hypothesis 22P_AP.** For every `K` there are natural numbers `x ≥ 1` and `v ≥ 1` such
that each of the `K + 1` numbers `x + j v` (`0 ≤ j ≤ K`) is a good slope prime
(`GoodSlopePrime`) larger than every prime of `S_b = S_ht ∪ 𝓗` (that is, larger than
`max S_b`).

It follows from the theorem of Green and Tao (*The primes contain arbitrarily long arithmetic
progressions*, Ann. of Math. 167 (2008), 481–547, Theorem 1.2, Szemerédi's theorem in the primes):
every set of primes of positive relative upper density contains arithmetic progressions of every
finite length. It applies to the good slope primes above `max S_b`, which have positive relative
density (`docs/research/nt-22p.md`, Proposition D). A progression of `K + 1 ≥ 2` distinct primes
has a nonzero common difference, which can be taken positive by reversing it. The two inputs are
the named statements `GreenTaoDense` and `GoodPrimeDensity` (`Hypotheses/GreenTao.lean`), which
imply this hypothesis (`goodPrimeAP_of_greenTaoDense`).

**Proved in Lean**: both inputs are theorems (`ZInQ.greenTaoDense`,
`ZInQ.Density.goodPrimeDensity`), and `ZInQKernel/MainGreenTao.lean` uses them to drop 22P from
the main theorem. The statement stays a named `Prop` so that the `_of_goodPrimeAP` variant of
`ZInQKernel/Main.lean` does not import the vendored library. -/
def GoodPrimeAP : Prop :=
  ∀ K : ℕ, ∃ x v : ℕ, 1 ≤ x ∧ 1 ≤ v ∧
    ∀ j ≤ K, GoodSlopePrime (x + j * v) ∧ ∀ q ∈ Mult.S_b, q < x + j * v

end ZInQ
