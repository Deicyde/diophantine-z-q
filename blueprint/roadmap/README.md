---
article_id: af_c6be9f76e8285425161078ad
open_statements: allowed
---

# Z is Diophantine in Q

This blueprint formalizes Theorem 1.1 of the 11/5 manuscript *ℤ is Diophantine in ℚ*
(`diophantine_zq.tex`): an integer polynomial in 292,890,231,905 variables, of degree below
$2\uparrow\uparrow 7$ and with coefficients below $2\uparrow\uparrow 8$, whose rational zero projection to the
first variable is exactly $\mathbb Z$. The chapters below follow the manuscript section by section. Each one
says where its material sits in the manuscript, what is proved in Lean, what the Lean takes as a hypothesis, and
what the checks of the manuscript's text found. Where the Lean takes a different route from the manuscript, the
chapter says so.

The [main theorem](main/main-theorem.md) proves Theorem 1.1 from two hypotheses, both inputs of the manuscript:
- the minimal form of the six-contact height estimate (Section 4), which the Lean in turn reduces to statements of
  the literature, most of them the ones the manuscript cites;
- pole completeness, the manuscript's Theorem 5.2 (Section 5), for the manuscript's polynomial. The manuscript
  derives it from its restricted converse theorem, Theorem 5.3, whose proof occupies Sections 7-9 and
  Appendices E-G.

Everything else is proved in Lean, with every finite computation checked by the Lean kernel.

## The manuscript, section by section

- **Section 1, the main theorem and proof structure** (`sec:main`, L52-140): [the main theorem and its
  hypotheses](main/README.md).
- **Section 2, a finite specification of the polynomial** (`sec:syntax`, L141-253) and **Appendix C, the literal
  finite-constructor specification** (L6666-6782): [the finite specification](syntax/README.md). Proved.
- **Section 3, the elliptic model of integer indices** (`sec:model`, L254-376): [the elliptic model](model/README.md).
  Proved, including the Mordell–Weil theorem for the generator curve.
- **Section 4, the six-contact height estimate** (`sec:height`, L377-972) and **Appendix H, the de Rham comparison**
  (L10936-11250): a hypothesis of the main theorem. [The statements of the literature it reduces
  to](height-decomposition/README.md) are listed by theory.
- **Section 5, the pole predicate and its converse input** (`sec:pole`, L973-1122): [pole
  completeness](main/pole-completeness.md), Theorem 5.2, for the manuscript's polynomial; the [pole
  obstruction](multiplication/pole-obstruction.md), Lemma 5.1, is proved.
- **Section 6, multiplication and the finite false-triple guard** (`sec:mult`, L1123-1759):
  [multiplication](multiplication/README.md). Proved. The manuscript's twenty-two-prime pattern (Proposition 6.2)
  is checked but not formalized: the Lean proves the completeness of multiplication by a different route,
  [long progressions of good primes](route-ap/README.md), which uses [Szemerédi's theorem in the
  primes](green-tao/README.md) and [the density of good slope primes](density/README.md).
- **Sections 7-9 and Appendices E-G, the restricted converse** (`sec:rc`, L1760-5744; L6825-10935): [the proof of
  Theorem 5.3](restricted-converse/README.md). Not formalized in Lean; the main theorem takes Theorem 5.3 as a
  hypothesis.
- **Section 10, exact precision computation and polynomial compilation** (`sec:compiler`, L5745-6093):
  [compilation](compiler/README.md). Proved.
- **Section 11, a variable-shift relation for ordinary values** (`sec:bridge`, L6094-6271):
  [assembly](assembly/README.md). Proved.
- **Section 12, the cutoff and polynomial size** (`sec:size`, L6272-6442): [size](size/README.md) and [primes in
  arithmetic progressions](progressions/README.md). Proved, with a larger cutoff than the manuscript's, from an
  effective Dirichlet theorem.
- **Section 13, consequences of the integer definition** (L6443-6589): not yet in the blueprint.
- **Appendices A, B and D** (dependency order, source identities, primary theorem applications; L6591-6665,
  L6783-6824): bookkeeping for the manuscript's citations, used by the chapters above.

## Route K

Until fork issue #77 the project replaced pole completeness by Route K, a variant of the pole polynomial whose
pole completeness followed from a rank hypothesis built on Tian–Yuan–Zhang and Gross–Zagier. Route K is retired:
its chapters are removed from this blueprint, and its Lean is kept at the tag `route-k-final`.
