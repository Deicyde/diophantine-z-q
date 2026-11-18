---
article_id: af_c6be9f76e8285425161078ad
open_statements: allowed
---

# Z is Diophantine in Q

This blueprint formalizes Theorem 1.1 of the 11/5 manuscript *ℤ is Diophantine in ℚ*:
an integer polynomial in 292,890,231,905 variables, of degree below $2\uparrow\uparrow 7$
and with coefficients below $2\uparrow\uparrow 8$, whose rational zero projection to the
first variable is exactly $\mathbb Z$.

The [main theorem](main/main-theorem.md) proves it from two explicitly stated hypotheses, both
inputs of the manuscript:
- the minimal form of the six-contact height estimate (the one instance of the manuscript's Theorem 4.1
  that the proof uses). It is not a published theorem: its proof combines refereed theorems and exact
  computations with new arguments, the manuscript's and this project's, reviewed only by AI models;
- pole completeness, the manuscript's Theorem 5.2: an explicit polynomial, whose rational zeros put two
  points on curves $y^2=x(x-\ell)(x+3\ell)$, has a zero for every suitably prepared input. The manuscript
  derives it from its restricted converse theorem (Theorem 5.3) by a simultaneous 2-descent. That
  derivation is not yet formalized here, and the proof of Theorem 5.3 is not formalized either.

The height hypothesis is in turn derived from statements of the literature, which
[the height-decomposition chapter](height-decomposition/README.md) lists. It may also be assumed in its $j$-form, a bound on the height of the Hauptmodul value (not a
published theorem) from which the minimal form is proved.

The manuscript's other inputs are proved, multiplication from the two hypotheses above. The
Mordell–Weil theorem for the generator curve, which the generator input uses and which was first
stated as a hypothesis, is proved too. Two of these proofs depart from the manuscript:
- The bound for the prime catalogue follows from an effective Dirichlet theorem, with a larger cutoff
  than the manuscript's.
- The manuscript's twenty-two-prime pattern is not needed. A change in the completeness proof, route
  AP, uses long arithmetic progressions of good primes instead. These come from Szemerédi's theorem in
  the primes, from a Lean proof of the Green–Tao theorem, and from a density theorem for those primes.

Everything else is proved, with every finite computation checked by the Lean kernel.

Until fork issue #77 the project replaced pole completeness by Route K: a variant of the pole polynomial
for the congruent number curves, whose pole completeness followed from a certified rank hypothesis
derived from Tian–Yuan–Zhang's Theorem 3.5(2) in one reading and from Gross–Zagier. Route K is retired.
Its Lean is kept at the tag `route-k-final`. Its chapters, listed last, are kept and marked as retired.

## Chapters

- [The main theorem and its hypotheses](main/README.md)
- [The finite specification of the polynomial](syntax/README.md)
- [The elliptic model of integer indices](model/README.md)
- [Multiplication and the finite false-triple guard](multiplication/README.md)
- [Exact precision computation and polynomial compilation](compiler/README.md)
- [Assembly and the ordinary-value relation](assembly/README.md)
- [The cutoff and polynomial size](size/README.md)
- [Primes in arithmetic progressions](progressions/README.md)
- [Long progressions of good primes replace the prime pattern (route AP)](route-ap/README.md)
- [Szemerédi's theorem in the primes (Green–Tao)](green-tao/README.md)
- [The density of good slope primes (Proposition D)](density/README.md)
- [The minimal height hypothesis from the literature](height-decomposition/README.md)

### Retired with Route K

- [Pole completeness from certified rank (Route K)](route-k/README.md)
- [The explicit system is the 2-Selmer group (Proposition 0)](selmer/README.md)
- [The row-5b determinant](rank-5b/README.md)
- [Rédei's formula for the 4-rank of class groups](redei/README.md)
- [The rank hypothesis as positive rank](rank/README.md)
