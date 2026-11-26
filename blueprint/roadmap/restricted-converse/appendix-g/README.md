---
article_id: af_6bbc497395116be3c56a2f11
---

# Appendix G: nonvanishing, normalization and the final family

Appendix G fixes the order of choices behind (3.3)–(3.9) in the proof of
[Theorem 5.3](../restricted-converse.md) and proves the propositions that Section 7 cites for them. The
even sources come first, with their depth already fixed by Appendix E: they give the bounded companion (3.3)
and, with (3.4) and (3.5), the genus lower bound. Only then is the odd minimum $\delta_o$ chosen. With
$\delta_o$ fixed, the odd stage symbols stabilize, the two-symbol address construction applies to the odd
and the even symbol, and one actual theta stage realizes the final family (3.9). The even upper transfer
uses the common Kato scalar; the final contradiction uses the common Heegner coordinate, through the
central identity (F.8) and the determinant argument of Section 9.

1. **Five primes.** Hoffstein–Luo gives nonvanishing twists with at most five new primes in every signed
   unit filter of even root number (Proposition G.1).
2. **The even upper transfer.** A unit of the normalized even symbol has an exact central valuation
   (F.1); cubes of units bound $v_2L_*$ at corank-zero parameters (F.2); a bounded partitionable
   companion follows (Proposition G.2, (F.3)).
3. **The odd minimum.** The genus lower bound (F.4) and visibility give the coarse bound (F.5); the odd
   minimum is attained and bounds the visible coefficients on an ultrafilter set (F.6); the units of the
   odd stage symbol are simple zeros with bounded genus index (F.7) (Proposition G.3).
4. **The seeds.** After $k$ and $K$ are fixed, the transported even source has a nonempty $K$-split
   seed, by a computation modulo eight, (G.4a)–(G.4d) (Proposition G.4).
5. **The address constructions.** Finite tables of the odd stage symbols stabilize on the ultrafilter
   (Proposition G.5); networks of primary auxiliaries make one or two symbols one at every nonzero
   address, by the degree count (G.1a) (Proposition G.6); one actual stage realizes the final family
   (Proposition G.7).
6. **The central identity** (F.8) for the corrected coordinate.

## Definitions

**The normalized even symbol.** For a fixed even source with coefficients $a(D)$, the integers
$v_2a(D)-\omega(D)$, over the nonzero coefficients, are bounded below by (E.9) of Appendix E, and with a
nonzero coefficient they have an attained minimum $\delta_e$. A *unit of the normalized symbol* is an
index $D$ at which $v_2a(D)-\omega(D)=\delta_e$. In Lean a unit is an index with $a(D)\ne0$ and
$v_2a(D)-\omega(D)=\delta$, as in `F1_unit` and `F2_bound`.

**Visible coefficients and the odd minimum.** At a theta stage $\theta$, of precision $M_\theta$, the odd
coefficient $a_{M_\theta}(D)$ is *visible* if $v_2a_{M_\theta}(D)<M_\theta$. Fix a nonprincipal ultrafilter
$\mathcal U$ on the stages. The *depth set* is the set of integers $r$ for which some bounded-weight
sequence of visible admissible $D_\theta$ has $v_2a_{M_\theta}(D_\theta)-\omega(D_\theta)=r$ for
$\mathcal U$-many $\theta$; the *odd minimum* $\delta_o$ is its least element. In Lean the depth set is
`ZInQ.Contrib.CloudB3RC53.AppGEndpoints.DepthSet`.

**Valid stages.** For an operator budget $|U|\le W_U$ and $R\ge2$, put $N_0=\max(0,\delta_o+W_U)$. A stage
is *valid* if (F.6) holds there through a weight $T\ge W_U+1$ with $T-C_{\rm coarse}\ge N_0+R$, and
$M_\theta\ge N_0+R$, $M_\theta>T+\delta_o$. Then the divisions required by the coefficient rules of
Appendix F hold at every Fourier index and every $U$ in the budget.

**The odd stage symbol.** For a cutoff $L$ and a stage, $\mathcal A_{M_\theta,L}(D)$ is defined for
positive squarefree $D$ with $\omega(D)\le L$: it is one if $D$ is in the coefficient filter and
$v_2a_{M_\theta}(D)=\delta_o+\omega(D)$, and zero otherwise.

## The items

- [Proposition G.1: nonvanishing with at most five primes](proposition-g-1-five-primes.md)
- Proposition G.2, a uniformly bounded partitionable companion, restates [Proposition
  7.14](../section-7/proposition-7-14-rough-companion.md) with its proof and is stated by the same
  declarations; its conclusion (F.3) is (3.3). Its other displays have their own pages:
  [(F.1): the central value at a unit of the normalized even symbol](equation-f-1-even-unit.md) and
  [(F.2): the even upper bound at a parameter of corank zero](equation-f-2-even-transfer.md).
- Proposition G.3, the odd minimum and every finite operator budget: no single declaration states it.
  (F.4) is [(3.6)](../section-7/equation-3-6-genus-lower-bound.md), stated by the same declaration; the
  manuscript leaves its constant $C_H$ undefined, and the Lean takes $C_{\rm per}+2$. The other displays
  have their own pages: [(F.5): the coarse lower bound](equation-f-5-coarse-bound.md),
  [(F.6): the attained odd minimum](equation-f-6-odd-minimum.md) and
  [(F.7): the units of the odd stage symbol](equation-f-7-unit-symbol.md). The valid stage for a finite
  operator budget is chosen by `ZInQ.Contrib.CloudB3RC53.AppGEndpoints.stageChoice_proof`.
- [Proposition G.4: the nonempty $K$-split seed, (G.4a)–(G.4d)](proposition-g-4-nonempty-seeds.md)
- [Proposition G.5: one table per cutoff on the ultrafilter](proposition-g-5-odd-stabilization.md)
- [Proposition G.6: the address constructions, (G.1a)](proposition-g-6-simultaneous-address.md)
- [Proposition G.7: one actual stage for the final family](proposition-g-7-final-stage.md)
- [(F.8): the central identity for the corrected coordinate](equation-f-8-central-identity.md)

(G.4a)–(G.4d) are on the page of Proposition G.4 and (G.1a) on that of Proposition G.6. The definitions
above are those of the proofs of Propositions G.2, G.3 and G.7.

## Items with no Lean statement

None. Every numbered item of Appendix G is stated by a declaration on main, except Propositions G.3 and
G.4, which no single declaration states. Each display of Proposition G.3 is stated, and the page of
(F.6) states its main clause, the attained odd minimum, through `oddMinimumF6_proof`. For Proposition
G.4 no page states the other clauses: `app_nonempty_seed` states only the seed clause, the Selmer
corank one of $E/K$ is `selmerCorankOneOverK_of`, the transported lower bound is
`transport_lower_bound`, and the nonempty odd seed is handled separately (`rc_of_oddEmptyUnit`,
`oddWitness_of_dataSpec`). Its page states the seed clause and names the other clauses in prose.

## Remaining hypotheses that cover Appendix G

These fields of [the remaining hypotheses](../remaining-hypotheses.md) cite lines of Appendix G in their
docstrings, with the kind each docstring gives:

- `PreLeaves.aux_factor` (definition and ELLIOT): the type data, the even sources with the coefficient
  rules, a unit seed at each prepared total type, and the meaning of partitionability; the proof of
  Proposition G.2. The seeds are asked only at the prepared types: the manuscript prepares them for every
  total type, which the docstring notes is false at negative types of root number $-1$. The leaf repairs
  this: `PreparedType` asks for a negative squarefree $d\equiv1\pmod8$ of that type, prime to the
  support, with analytic rank zero, and the proof uses only the total type that actually occurs.
- `PreLeaves.even_upper` (ELLIOT): (3.3a) at the units of the even symbol, (3.2), and the cubes of units
  at partitionable parameters; the passage of (F.1) and (F.2).
- `PostLeaves.address` (ELLIOT and GLUE, with definitions): in the remaining branch, the label data with
  the intrinsic odd filter, a fresh prime of $k$, models of the odd stage source and of the transported
  even source, the filters, the $K$-split seed in the conditional form of Lemma 7.16, and the even
  reading, the conclusion of (F.1) for the transported source; the lines from (F.1) through Proposition
  G.7.
- `RCLeaves.hlPrint` (PRINT): the theorem of Hoffstein and Luo, used in Proposition G.1.

## Sources

- [Appendix G](../../../sources/manuscript.md#appendix-g)
