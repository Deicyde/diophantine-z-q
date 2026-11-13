---
article_id: af_c6be9f76e8285425161078ad
open_statements: allowed
---

# Z is Diophantine in Q

This blueprint formalizes Theorem 1.1 of the 11/5 manuscript *ℤ is Diophantine in ℚ*:
an integer polynomial in 292,890,231,905 variables, of degree below $2\uparrow\uparrow 7$
and with coefficients below $2\uparrow\uparrow 8$, whose rational zero projection to the
first variable is exactly $\mathbb Z$.

The theorem is proved from two explicitly stated arithmetic hypotheses, the six-contact height
estimate and a certified rank hypothesis for congruent number curves, whose proofs lie far
outside current formal libraries. The positive-rank form of the class-number hypothesis, and so
the certified rank hypothesis, also follows from three statements about L-series of elliptic
curves: two textbook theorems (a functional equation on the critical strip and Gross–Zagier) and
Tian–Yuan–Zhang's row 5b, which rests on Proposition N, an unpublished argument written for this
project and not refereed. With that rank
hypothesis or those three statements, the height hypothesis may also be assumed in its $j$-form, a
bound on the height of the Hauptmodul value (not a published theorem) from which the minimal form
is proved. The manuscript's other
inputs are proved. Pole completeness
follows from the certified rank hypothesis for a variant of the manuscript's pole polynomial,
and also from positive rank of the congruent number curves that hypothesis covers, or of only the
two curves the descent constructs; the bound for the prime catalogue follows from an effective
Dirichlet theorem; the Mordell–Weil theorem for the generator curve, first stated as a
hypothesis, is proved; and the
twenty-two-prime pattern is not needed: a change in the completeness proof, route AP, uses
long arithmetic progressions of good primes instead, which come from Szemerédi's theorem in the
primes (from a Lean proof of the Green–Tao theorem) and a density theorem for those primes.
The passage from positive rank to points in every Selmer class rests on the complete 2-descent
and the Mordell–Weil theorem for these curves, and Smith's row-5b identity and Rédei's formula
let the hypothesis be stated in Tian, Yuan and Zhang's terms; all four are proved.
Everything else is proved, with every finite computation checked by the Lean kernel.

## Chapters

- [The main theorem and its hypotheses](main/README.md)
- [The finite specification of the polynomial](syntax/README.md)
- [The elliptic model of integer indices](model/README.md)
- [Multiplication and the finite false-triple guard](multiplication/README.md)
- [Exact precision computation and polynomial compilation](compiler/README.md)
- [Assembly and the ordinary-value relation](assembly/README.md)
- [The cutoff and polynomial size](size/README.md)
- [Primes in arithmetic progressions](progressions/README.md)
- [Pole completeness from certified rank (Route K)](route-k/README.md)
- [Long progressions of good primes replace the prime pattern (route AP)](route-ap/README.md)
- [Szemerédi's theorem in the primes (Green–Tao)](green-tao/README.md)
- [The density of good slope primes (Proposition D)](density/README.md)
- [The explicit system is the 2-Selmer group (Proposition 0)](selmer/README.md)
- [The row-5b determinant](rank-5b/README.md)
- [Rédei's formula for the 4-rank of class groups](redei/README.md)
- [The rank hypothesis as positive rank](rank/README.md)
