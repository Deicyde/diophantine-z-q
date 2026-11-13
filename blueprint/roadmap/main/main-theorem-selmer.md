---
article_id: af_9ce1e3b54e131b088182fed5
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRankSel, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_certifiedRank5b, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_goodPrimeDensity, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel_greenTaoDense, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRank5b
---

# The main theorem from the Selmer form of the rank hypothesis

Assume the minimal height hypothesis and the Selmer form CR₃^Sel of the certified rank
hypothesis. Then the target statement holds.

CR₃^Sel speaks of the 2-Selmer group of the congruent number curve, defined by local solubility
of its 2-coverings, instead of the explicit linear system in Legendre symbols, and asks that
every Selmer class come from a rational point. The theorem also holds under the minimal height
hypothesis, CR₃^Sel and the twenty-two-prime pattern; under the minimal height hypothesis,
CR₃^Sel, Szemerédi's theorem in the primes and the positive relative upper density of the good
slope primes; and under the minimal height hypothesis, CR₃^Sel and that density statement. Since CR₃^Sel
follows from the row-5b form CR₃^5b of the hypothesis, the theorem holds as well under the minimal
height hypothesis and CR₃^5b, and under the minimal height hypothesis, CR₃^5b and the
twenty-two-prime pattern.

**Proof sketch.** Proposition 0 identifies the explicit system with the 2-Selmer group, so
CR₃^Sel implies CR₃; then apply [the main theorem from two hypotheses](main-theorem-two-hypotheses.md)
(or, with the twenty-two-prime pattern, [the main theorem](main-theorem.md), and with the two
statements of route AP, its intermediate forms). Under CR₃^5b, Corollary 4.4 first gives CR₃^Sel,
and the form with the minimal height hypothesis and CR₃^Sel applies (with the twenty-two-prime
pattern, the form with CR₃^Sel and the pattern).

## Depends on

- [The target statement](frozen-target.md)
- [The minimal height hypothesis](six-contact-min.md)
- [The Selmer form of the certified rank hypothesis](../selmer/certified-rank-sel.md)
- [The certified rank hypothesis in row-5b form](../rank-5b/certified-rank-5b.md)

## Proof depends on

- [CR₃ from its Selmer form](../selmer/certified-rank-of-sel.md)
- [The main theorem from two hypotheses](main-theorem-two-hypotheses.md)
- [The main theorem](main-theorem.md)
- [CR₃^Sel from the row-5b hypothesis](../rank-5b/certified-rank-sel-of-5b.md)

## Sources

- [Theorem 1.1 and Lemma 1.2](../../sources/manuscript.md#theorem-11)
