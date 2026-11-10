---
article_id: af_9b19767b2c5b68b78591a8d2
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_goodPrimeDensity, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_greenTaoDense, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_goodPrimeAP
---

# The main theorem from two hypotheses

Assume the minimal height hypothesis and the certified rank hypothesis CR₃. Then the target
statement holds: some integer polynomial in $292{,}890{,}231{,}905$ variables, of degree below
$2\uparrow\uparrow7$ and with coefficients below $2\uparrow\uparrow8$, has rational zero projection
to its first variable exactly $\mathbb Z$.

The polynomial is the same as in [the main theorem](main-theorem.md); only the proof of the
completeness of its multiplication template changes. The twenty-two-prime pattern is not
assumed: route AP proves completeness from long arithmetic progressions of good slope primes
(the statement 22P_AP), and 22P_AP follows from Szemerédi's theorem in the primes and
Proposition D, both proved. On the way the theorem holds under each set of hypotheses
(i) the minimal height hypothesis, CR₃ and 22P_AP; (ii) the minimal height hypothesis, CR₃,
Szemerédi's theorem in the primes and the positive relative upper density of the good slope
primes; (iii) the minimal height hypothesis, CR₃ and that density statement alone.

**Proof sketch.** Under 22P_AP, Proposition AP writes every integer as a sum of three slopes
satisfying the weakened condition 2′, and the completeness of the multiplication template under
the weakened slope representation (with Lemma P absorbing a pole at an old prime) replaces the
completeness step of the assembly lemma; pole completeness comes from CR₃ as in the main theorem.
This gives (i). The dense form of Green–Tao and the density statement give 22P_AP, which gives
(ii); Szemerédi's theorem in the primes is proved, which gives (iii); Proposition D proves the
density statement, which gives the theorem.

## Depends on

- [The target statement](frozen-target.md)
- [The minimal height hypothesis](six-contact-min.md)
- [The certified rank hypothesis](certified-rank.md)

## Proof depends on

- [The main theorem](main-theorem.md)
- [Pole completeness from the certified rank hypothesis](../route-k/pole-completeness-from-cr3.md)
- [The statement 22P_AP](../route-ap/good-prime-ap.md)
- [Proposition AP](../route-ap/proposition-ap.md)
- [Completeness under the weakened slope representation](../route-ap/completeness-ap.md)
- [The assembly lemma under the weakened slope representation](../route-ap/assembly-ap.md)
- [22P_AP from Green–Tao and Proposition D](../route-ap/good-prime-ap-from-green-tao.md)
- [Szemerédi's theorem in the primes](../green-tao/dense-theorem.md)
- [Proposition D](../density/proposition-d.md)

## Sources

- [Theorem 1.1 and Lemma 1.2](../../sources/manuscript.md#theorem-11)
