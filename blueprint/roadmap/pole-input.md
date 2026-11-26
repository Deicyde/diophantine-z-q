---
article_id: af_91c0ceba51fd419ca2adadf7
---

# The pole input

The multiplication template and the six local tests of the construction need, for completeness, that a
certain explicit polynomial
$Q_{\rm pole}$ has a rational zero for every suitably prepared input $B$
([pole completeness](main/pole-completeness.md)). A zero is a pair of rational points, with
prescribed abscissas, on two elliptic curves built from $B$; both routes get them from rank statements
through a 2-descent. There are two routes to it, and each
gives a headline theorem.

**Elliot's route.** This is the manuscript's own argument, for the manuscript's polynomial, whose zeros put
points on curves $E_\ell:y^2=x(x-\ell)(x+3\ell)$.
- [Theorem 5.2 from Theorem 5.3](pole-completeness-from-5-3/README.md): a simultaneous 2-descent builds two
  curves $E_n$, $E_{n\theta}$ whose 2-Selmer groups have dimension $3$; Lemma 5.4 (from the Cassels–Tate
  pairing) turns that into Selmer corank one, the restricted converse gives analytic rank one, and
  Silverman's rank-one implication gives rank one. This derivation is proved in Lean from those three
  inputs.
- [Theorem 5.3, the restricted converse](restricted-converse/README.md): the manuscript's own theorem, proved
  in its Sections 7–9 and Appendices E–G. The Lean reduces it to the results it cites and one structure of
  remaining hypotheses, which are not proved, so the main theorem still takes Theorem 5.3 as a hypothesis.

**The congruent-number route.** A variant of the pole polynomial, for the congruent number curves
$C_\ell:y^2=x(x-\ell)(x+\ell)$, keeps the elementary direction (Lemma 5.1) and replaces the restricted
converse by the [certified rank hypothesis](main/certified-rank.md).
- [Pole completeness from certified rank](route-k/README.md): an explicit descent, with the 2-Selmer groups
  written as linear systems in Legendre symbols ([Proposition 0](selmer/README.md)), reduces pole completeness
  to certified rank.
- [The row-5b determinant](rank-5b/README.md), [Rédei's formula](redei/README.md) and
  [the rank hypothesis as positive rank](rank/README.md) derive certified rank from Tian–Yuan–Zhang's
  Theorem 3.5(2) in reading A and from Gross–Zagier.

The Lean of this route is kept at the tag `route-k-final`; each of its pages says whether its declarations
are still on this fork's main.
