---
article_id: af_c6be9f76e8285425161078ad
open_statements: allowed
---

# Z is Diophantine in Q

This blueprint formalizes Theorem 1.1 of the 11/5 manuscript *ℤ is Diophantine in ℚ*:
an integer polynomial in 292,890,231,905 variables, of degree below $2\uparrow\uparrow 7$
and with coefficients below $2\uparrow\uparrow 8$, whose rational zero projection to the
first variable is exactly $\mathbb Z$.

The theorem is proved from explicitly stated arithmetic hypotheses: the six-contact
height estimate, pole completeness and a twenty-two-prime pattern, whose proofs lie far
outside current formal libraries, and a bound for the prime catalogue, which an effective
Dirichlet theorem proves. The Mordell–Weil theorem for the generator curve, first stated as
a fifth hypothesis, is proved. Everything else is to be proved, with every finite computation
checked by the Lean kernel.

## Chapters

- [The main theorem and its hypotheses](main/README.md)
- [The finite specification of the polynomial](syntax/README.md)
- [The elliptic model of integer indices](model/README.md)
- [Multiplication and the finite false-triple guard](multiplication/README.md)
- [Exact precision computation and polynomial compilation](compiler/README.md)
- [Assembly and the ordinary-value relation](assembly/README.md)
- [The cutoff and polynomial size](size/README.md)
- [Primes in arithmetic progressions](progressions/README.md)
