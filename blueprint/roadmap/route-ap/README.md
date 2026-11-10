---
article_id: af_d02f6b76a28d0c3198d0d6e3
---

# Route AP: progressions of good primes in place of the prime pattern

The completeness of the multiplication template needs every integer to be a sum of three good
slopes, the [slope representation](../multiplication/completeness/slope-representation.md). The
manuscript obtains it from the twenty-two-prime pattern of Proposition 6.2, whose proof uses the
Green–Tao–Ziegler theory of linear equations in primes. Route AP replaces the twenty-two-prime
pattern by the statement 22P_AP, that the good slope primes contain arbitrarily long arithmetic
progressions, through a change in the completeness proof only: **the polynomial is unchanged**,
and so are the slope predicate and soundness. Since 22P_AP follows from Szemerédi's theorem in the
primes and the positive density of the good slope primes, both proved here, the twenty-two-prime
pattern is no longer a hypothesis of the main theorem.

The obstacle is the common difference: a progression of many primes has a difference divisible by
every small prime to a high power, so its slopes have poles at the old primes $S_b$, which
condition 2 of the slope representation forbids. Lemma P shows that such a pole is harmless: the
parameter $q$ of the slope certificate, chosen $\ell$-adically close to a square root of
$R_0^{-1}$, absorbs it.

## Lemma P

- [The hypotheses of Lemma P](pole-absorption-hypotheses.md)
- [Lemma P: a pole at an old prime is absorbed by the parameter $q$](lemma-p.md)
- [Lemma P, part (3): the valuation of the pole input](lemma-p-valuation.md)

## The modified completeness of the multiplication template

Field 2′ allows, at each old prime, either the bounds of condition 2 or the hypotheses of Lemma P.
The completeness proof of the multiplication chapter goes through with one change: at the old
primes where a slope has a pole, the weak approximation step puts $q$ in the ball of Lemma P(2)
instead of making $v_\ell(q)\ge C_\ell$. Everything else (the shifts at the selected primes, the
integrality of the tests at the old primes, positivity and smallness of the pole input, the guard)
is reused unchanged.

- [Slopes with poles at the old primes: field 2′](good-slope-ap.md)
- [The slope representation under field 2′](slope-representation-ap.md)
- [The slope representation implies its form under field 2′](slope-representation-ap-of-slope-representation.md)
- [Weak approximation with residue targets](weak-approximation-targets.md)
- [Valuations of the pole input under field 2′](pole-input-valuations-ap.md)
- [Completeness of the slope certificate under field 2′](slope-completeness-ap.md)
- [Completeness of the multiplication template under field 2′](completeness-ap.md)
- [Correctness of the multiplication template under field 2′](multiplication-exact-ap.md)
- [The ordinary-value relation under field 2′](value-relation-ap.md)
- [The assembly lemma under field 2′](assembly-ap.md)

## Proposition AP

A progression of good slope primes long enough to contain the fourteen numerators of the slopes
$u/v$ and $A+10-u/v$ gives, with the constant slope $-10$, a representation of $A$.

- [The statement 22P_AP: long progressions of good slope primes](good-prime-ap.md)
- [A slope with prime numerators satisfies field 2′](progression-slope.md)
- [Proposition AP: progressions of good slope primes give the slope representation](proposition-ap.md)

## 22P_AP from Green–Tao

The good slope primes have positive relative density
([Proposition D](../density/README.md)), and every such set of primes contains arbitrarily long
progressions ([Szemerédi's theorem in the primes](../green-tao/README.md)).

- [22P_AP from Green–Tao and Proposition D](good-prime-ap-from-green-tao.md)
