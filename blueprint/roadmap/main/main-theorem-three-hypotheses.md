---
article_id: af_0be94ccf3fca69a8d9322f8c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.exists_bounded_integer_polynomial_defining_integers_of_poleCompleteness
---

# The main theorem from three hypotheses

Assume the minimal height hypothesis, pole completeness and the twenty-two-prime pattern. Then the
target statement holds: some integer polynomial in $292{,}890{,}231{,}905$ variables, of degree below
$2\uparrow\uparrow7$ and with coefficients below $2\uparrow\uparrow8$, has rational zero projection to
its first variable exactly $\mathbb Z$.

This is the form of the main theorem closest to the manuscript's inputs.
- The minimal height hypothesis is the one instance $S=S_{\rm mul}$, $R=D$ of the six-contact height
  estimate that the proof uses, so the theorem holds in particular under the six-contact estimate
  itself ([the six-contact estimate implies its minimal form](six-contact-min-of-estimate.md)).
- Pole completeness is the manuscript's Theorem 5.2, for the manuscript's polynomial.
- The twenty-two-prime pattern enters only through the
  [slope representation](../multiplication/completeness/slope-representation.md).
- The catalogue bound, a step of the manuscript's size bounds (Proposition 12.1), is replaced by a theorem
  with a larger cutoff
  ([the catalogue bound holds](../progressions/catalogue-instance.md)): every unit class modulo $W$
  contains twenty-two primes $p$ with $324<p<2^{W^8}$, by an effective Dirichlet theorem, where the
  manuscript has the cutoff $2^{W^3}$.
- The bound on the addition and multiplication nodes of the universal halting circuit is a finite
  check proved in the compiler chapter.

The twenty-two-prime pattern is not needed at all. Route AP proves the completeness of the
multiplication template from long progressions of good slope primes, which Szemerédi's theorem in the
primes and Proposition D supply. So the target holds under the minimal height hypothesis and pole
completeness alone ([the main theorem](main-theorem.md)).

## Depends on

- [The target statement](../statements/frozen-target.md)
- [The minimal height hypothesis](../multiplication/certificate/six-contact-min.md)
- [Pole completeness](../statements/pole-completeness.md)
- [The twenty-two-prime pattern](../statements/prime-pattern.md)
- [Node statistics of the halting circuit and the power template](../compiler/natural/universal/halting-node-check.md)
- [Exact node statistics of the halting circuit](../compiler/natural/universal/halting-node-exact.md)

## Proof depends on

- [The assembly lemma](../assembly/assembly-lemma.md)
- [The twenty-two-prime pattern gives the slope representation](../multiplication/completeness/slope-representation-from-pattern.md)
- [The catalogue bound holds](../progressions/catalogue-instance.md)

## Sources

- [Theorem 1.1 and Lemma 1.2](../../sources/manuscript.md#theorem-11)
