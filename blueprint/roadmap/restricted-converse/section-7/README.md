---
article_id: af_97f524cf206504624584a763
---

# Section 7: the restricted converse and its dependency order

Section 7 begins the proof of [Theorem 5.3](../restricted-converse.md) for one fixed admissible $\ell$
and $E=E_\ell:y^2=x(x-\ell)(x+3\ell)$. It fixes a modular parametrization of $E$ and the normalized
central values $L_*(h)$ of the quadratic twists $E^{(h)}$, records [the opening
reduction](../opening-reduction.md) (root number $-1$), and then lays out the proof in its dependency
order:

1. **The even coefficient bound.** One fixed-form scalar built from Kato's Euler system controls
   $v_2L_*(h)$ on binary families of twists (Proposition 7.2). Every signed unit filter contains a
   nonvanishing twist (Proposition 7.3). A missing-address argument on cubes of unit symbols then bounds
   $v_2L_*$ above at partitionable parameters (Proposition 7.13), hence at a bounded companion of each
   prepared parameter (Proposition 7.14).
2. **The finite combinatorics.** Coefficient symbols on typed graphs, the rules they obey, prime
   realization, minimum seeds and the two address lemmas (Lemmas 7.6–7.12).
3. **The genus lower bound.** Two explicit Gross–Zagier comparisons and the arithmetic estimate of
   Sections 8–9 bound the genus index below, uniformly, before any odd normalization
   (Proposition 7.15, that is (3.4)–(3.6)).
4. **The odd forms.** A fixed visible witness $D_w$, arbitrarily advanced theta stages (3.7) and the
   theta coefficient congruence (3.8) give an attained odd minimum depth.
5. **The final choices.** If the odd symbol is a unit at the empty configuration, (RC) follows at
   $D=1$. Otherwise a final companion $k$ with $L(E^{(k)},1)\ne0$ is fixed, $E$ has Selmer corank one
   over $K=\mathbb Q(\sqrt k)$, the even source of $E^{(k)}$ has a nonempty $K$-split unit seed
   (Lemma 7.16), and one binary family of twists meets both coefficient tests (Proposition 7.17, that
   is (3.9)). The determinant argument that finishes the proof is in Section 9.

## Definitions

**Why this family (Remark 7.1).** The congruence $\ell\equiv11\pmod{12}$ comes from pole completeness:
its proof applies Theorem 5.3 to exactly two such parameters, whose Selmer coranks are one by
[Lemma 5.4](../../pole-completeness-from-5-3/lemma-5-4.md). The fixed $\ell$ is odd, prime to $3$ and
not a square. The proof uses the full rational two-torsion of $E_\ell$, the absence of complex
multiplication, the rational two-isogeny and the roots $0,\ell,-3\ell$ (in Lemma 7.16). Constants may
depend on the fixed curve; nothing is claimed uniformly in $\ell$. In Lean the curve is `Ecurve ℓ` and
the admissibility condition is `Adm ℓ`.

**Typed graphs (Definition 7.4).** Fix the finite support $S$ of a coefficient source, containing
$2$, and the quadratic characters that read its coefficients. The *type* of a prime $p\notin S$
records its values under these characters and its unit squareclasses at $S$, including its class
modulo $8$; the realizable types lie in a finite elementary abelian $2$-group $\mathcal L$. A
*compatible typed graph* is a finite ordered vertex set $V$, a realizable type $\ell_v$ for each vertex,
and residue bits $z_{vw}\in\mathbb F_2$, with $z_{vw}=0$ or $1$ as $(p_v/p_w)=1$ or $-1$ for prime
representatives. One bit per pair is free; the other is fixed by
$z_{vw}+z_{wv}=\epsilon_v\epsilon_w$, where $\epsilon_v=(p_v-1)/2\bmod 2$ is part of the type. A filter
prescribes the total type $\sum_v\ell_v$. *Contracting* $v,w$ replaces them by one vertex whose type and
external incidences are the sums of theirs; the internal bit is dropped. A vertex is *primary* if its
type is neutral, and *neutral relative to a graph* if moreover all its incidences are zero. Two symbols
may read projections of one common type group. In Lean, typed graphs are
`ZInQ.Manuscript.RC.Symbols.Config`, with `Config.Compatible`, `Config.contract` and `Config.total`;
the alphabet is an additive group with a sign coordinate $\epsilon:\mathcal L\to\mathbb F_2$, a primary
vertex is one of type $0$, and the types of primes are `TypeData`.

**Coefficient symbols (Definition 7.5).** A coefficient source $a$ and a normalized depth $\delta$ give
the symbol $A(D)=1$ if $v_2a(D)=\delta+\omega(D)$ and $A(D)=0$ if $v_2a(D)>\delta+\omega(D)$, on allowed
positive squarefree indices $D$; $A$ is zero off the source's filter. For the even source the
coefficient is rational after exact phase removal; for an odd source one uses an integer
representative modulo the retained power $2^{M_\theta}$, and only within a finite cutoff, so that the
limit symbol is a function on typed graphs. In Lean, `ZInQ.Manuscript.RC.Symbols.coeffSymbol` is $1$
exactly when $D$ is in the filter, $a(D)\ne0$ and $v_2a(D)=\delta+\omega(D)$, and $0$ otherwise, so the
lower bound that makes the two cases exhaustive is not built in; on typed graphs the symbol is
`ZInQ.Contrib.CloudB3RC53.CoefficientDictionary.symb`, the reading of any prime realization.

**Unit seeds and partitionable lists (Definition 7.8).** A *unit seed* is a compatible typed graph with
symbol one, and a *minimum nonempty seed* is one of least positive vertex count. A nonempty list of
primes is *partitionable* if its vertices split into nonempty clusters, each with a contraction tree,
such that the contracted graph is a unit seed; the trees form a *contraction certificate*. In Lean these
are `IsUnitSeed`, `IsMinSeed` and `IsPartitionable` (a forest on the vertices whose contraction has
symbol one).

**Addresses and terminal polynomials (Definition 7.10).** For $b\ge1$ an *address* is
$x\in\mathbb F_2^b$. A vertex with activation $\lambda\in(\mathbb F_2^b)^*\setminus\{0\}$ is present at
$x$ exactly when $\lambda(x)=1$; stationary vertices are present at every address. At a fixed address,
with types and external data fixed, the symbol is a function of the free pair bits between the active
vertices; its multilinear polynomial over $\mathbb F_2$ is the *terminal polynomial*. In Lean an
address is `ZInQ.Manuscript.RC.Boolean.Address`, the active configuration is `Config.at`, and only the
nonvanishing of the terminal polynomial is named, as `TerminalNonzero`: some change of the pair bits
makes the symbol one.

## The items

- [Proposition 7.2: the fixed-form even scalar (3.2)](proposition-7-2-even-scalar.md), with (3.1)
- [Proposition 7.3: nonvanishing in a signed unit filter](proposition-7-3-nonvanishing.md)
- [Lemma 7.6: the coefficient rules](lemma-7-6-coefficient-rules.md)
- [Lemma 7.7: finite realization](lemma-7-7-finite-realization.md)
- [Lemma 7.9: minimum seeds and contraction certificates](lemma-7-9-minimum-seeds.md)
- [Lemma 7.11: one symbol with a stationary base](lemma-7-11-one-symbol-address.md)
- [Lemma 7.12: two symbols on one address family](lemma-7-12-two-symbol-address.md)
- [(3.3a): the bound at a unit of the even symbol](equation-3-3a-unit-symbol-bound.md)
- [Proposition 7.13: the partitionable even upper bound (3.3b)](proposition-7-13-even-upper-bound.md)
- [Proposition 7.14: a bounded companion (3.3)](proposition-7-14-rough-companion.md)
- Proposition 7.15, the genus bound before odd normalization, asserts (3.4)–(3.6); no single
  declaration states it, and each display has its own page:
  [(3.4): the height comparison](equation-3-4-height-comparison.md),
  [(3.5): the arithmetic lower bound](equation-3-5-arithmetic-lower-bound.md),
  [(3.6): the genus lower bound](equation-3-6-genus-lower-bound.md)
- [(3.7): arbitrarily advanced stages](equation-3-7-advanced-stages.md)
- [(3.8): the odd theta coefficients](equation-3-8-theta-coefficients.md)
- [Lemma 7.16: the nonempty $K$-split seed](lemma-7-16-k-split-seed.md)
- [Proposition 7.17: one family for the two coefficient tests (3.9)](proposition-7-17-final-family.md)

The display (RC) is [Theorem 5.3](../restricted-converse.md). Definitions 7.4, 7.5, 7.8 and 7.10 and
Remark 7.1 are on this page. The displays (3.2), (3.3b), (3.3) and (3.9) are the conclusions of
Propositions 7.2, 7.13, 7.14 and 7.17 and share their pages; (3.1) is on the page of Proposition 7.2.

## Items with no Lean statement

None. Every numbered item of Section 7 is stated by a declaration on main, though the last clause of
(3.7) only through Appendix F's (O.2); see that page.

## Remaining hypotheses that cover Section 7

These fields of [the remaining hypotheses](../remaining-hypotheses.md) cite lines of Section 7 in their
docstrings, with the kind each docstring gives:

- `PreLeaves.stage_support` (definitions): the fixed support and the prepared filter.
- `PreLeaves.aux_factor` (definition and ELLIOT): the type data, the even sources for each prepared
  total type with the coefficient rules, a unit seed at each prepared type, and the meaning of
  partitionability; Definitions 7.4–7.8 and Propositions 7.13–7.14. The seeds are asked only at the
  prepared types, not at every total type as in the manuscript.
- `PreLeaves.even_upper` (ELLIOT): (3.3a) at the units of the even symbol, (3.2), and the cubes of units
  at partitionable parameters; Proposition 7.13.
- `PreLeaves.odd_staged` (GLUE, ELLIOT, PRINT and definitions): the normalization of $L_*$, the genus
  partner, the conditions on the final $k$, the fixed witness and its stages, and the theta side of
  (3.8); the passage on the fixed witness and the odd forms.
- `PreLeaves.eq35` (ELLIOT and GLUE): the inputs of (3.5), whose proof is in Sections 8–9.
- `PostLeaves.companion` (derived from printed results, and a definition): the final companion $k$.
- `PostLeaves.address` (ELLIOT and GLUE): the inputs of the address construction in the remaining
  branch, including the $K$-split seed of Lemma 7.16.
- `RCLeaves.hlPrint` (PRINT): Hoffstein–Luo, used in Proposition 7.3.
- `RCLeaves.shimuraConjugates` and `RCLeaves.liMultiplicityOne` (PRINT), `RCLeaves.carayolEulerFactors`
  and `RCLeaves.faltingsRigidity` (GLUE): with Theorem A of Breuil–Conrad–Diamond–Taylor they give the
  newform of $E$, the modular realization at the start of the section.

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
