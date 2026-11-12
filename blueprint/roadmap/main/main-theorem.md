---
article_id: af_0be94ccf3fca69a8d9322f8c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.exists_bounded_integer_polynomial_defining_integers_of, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactEstimate, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_addMulBound, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_twoSlopePattern, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness, ZInQ.exists_bounded_integer_polynomial_defining_integers_of_nodeCheck
---

# The main theorem

Assume the minimal height hypothesis, the certified rank hypothesis CR₃ and the
twenty-two-prime pattern. Then the target statement holds: some integer polynomial in
$292{,}890{,}231{,}905$ variables, of degree below $2\uparrow\uparrow7$ and with coefficients below
$2\uparrow\uparrow8$, has rational zero projection to its first variable exactly $\mathbb Z$.

The minimal height hypothesis is the one instance $S=S_{\rm mul}$, $R=D$ of the six-contact
height estimate that the proof uses, so the theorem holds in particular under the six-contact
estimate itself ([the six-contact estimate implies its minimal form](six-contact-min-of-estimate.md)).
CR₃ enters only through pole completeness, which it implies for the Route K pole polynomial
([pole completeness from the certified rank hypothesis](../route-k/pole-completeness-from-cr3.md));
so the theorem also holds under pole completeness in place of CR₃.
The twenty-two-prime pattern enters only through the
[slope representation](../multiplication/completeness/slope-representation.md); since the
[two-slope pattern](two-slope-pattern.md) also gives the slope representation, the theorem
holds under the two-slope pattern in place of the twenty-two-prime
pattern. The manuscript's fourth input, the catalogue bound, is replaced by a theorem with a
larger cutoff ([the catalogue bound holds](../progressions/catalogue-instance.md)): every unit
class modulo $W$ contains twenty-two primes $p$ with $324<p<2^{W^8}$, by an effective Dirichlet
theorem, where the manuscript has the cutoff $2^{W^3}$.
The bound on the addition and multiplication nodes of the universal halting circuit, and the
circuit's exact node statistics, are finite checks proved in the compiler chapter; the theorem
holds as well with either one added as a hypothesis.

The twenty-two-prime pattern is not needed at all: route AP proves the completeness of the
multiplication template from long progressions of good slope primes, which Szemerédi's theorem in
the primes and Proposition D supply, so the target holds under the minimal height
hypothesis and CR₃ alone ([the main theorem from two hypotheses](main-theorem-two-hypotheses.md)).
The present form, which keeps the manuscript's prime pattern, uses none of that material.

## Depends on

- [The target statement](frozen-target.md)
- [The minimal height hypothesis](six-contact-min.md)
- [The certified rank hypothesis](certified-rank.md)
- [The twenty-two-prime pattern](prime-pattern.md)
- [Node statistics of the halting circuit and the power template](../compiler/natural/universal/halting-node-check.md)
- [Exact node statistics of the halting circuit](../compiler/natural/universal/halting-node-exact.md)

## Proof depends on

- [The assembly lemma](../assembly/assembly-lemma.md)
- [Pole completeness from the certified rank hypothesis](../route-k/pole-completeness-from-cr3.md)
- [The twenty-two-prime pattern gives the slope representation](../multiplication/completeness/slope-representation-from-pattern.md)
- [The catalogue bound holds](../progressions/catalogue-instance.md)

## Sources

- [Theorem 1.1 and Lemma 1.2](../../sources/manuscript.md#theorem-11)
