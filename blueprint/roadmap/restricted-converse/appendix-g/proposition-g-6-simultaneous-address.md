---
article_id: af_e1f1080675f1c6f7b77d6b40
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Symbols.address_general, ZInQ.Manuscript.RC.Symbols.address_general_one, ZInQ.Manuscript.RC.Symbols.degree_count, ZInQ.Manuscript.RC.Symbols.final_family_graphs
---

# Proposition G.6: the address constructions, (G.1a)

Assume that $A_1$ and $A_2$ satisfy [the coefficient rules](../section-7/lemma-7-6-coefficient-rules.md).
Let $b\ge1$ and let $\Gamma$ be a compatible typed graph in which every vertex is stationary or carries
a linear form on $\mathbb F_2^b$, its activation; write $\Gamma_x$ for the active configuration at $x$.
Suppose:

- (anchors) for every nonzero linear form $\lambda$, some vertex is present at every $x$ with
  $\lambda(x)=1$;
- (balancing) for every $y\ne0$ and all distinct vertices $a,c$ active at $y$, some set $R$ of vertices
  has an even number of members present at every address and meets the vertices active at $y$ exactly
  in $a$ and $c$;
- at every $x\ne0$, $\Gamma_x$ has nonzero terminal polynomial for $A_1$ and for $A_2$.

Then there is a compatible $\Gamma'\supseteq\Gamma$ in which the vertices of $\Gamma$, their types, mutual
bits and activations are unchanged, every new vertex has type $0$ and a nonzero activation, so that none
is present at $x=0$, and $A_1(\Gamma'_x)=A_2(\Gamma'_x)=1$ at every $x\ne0$. `address_general_one` is the
same statement for one symbol, proved with singular programs alone.

In the proof, at each $x\ne0$ one chooses a coefficient-one monomial $\prod_eX_e^{n_{x,e}}$,
$n_{x,e}\in\{0,1,2\}$, of the product of the top homogeneous parts of the two terminal polynomials in the
ordinary polynomial ring, and installs, on disjoint auxiliary vertices, a singular network for each
$n_{x,e}=2$ and a varying network $V^{\varepsilon_{x,e}}_{x,e}$ for each $n_{x,e}=1$. With
$\Gamma_y(\varepsilon)$ the resulting graph at $y$, the sum in $\mathbb F_2$
$$\sum_\varepsilon\prod_{y\ne0}\prod_{s=1}^2A_s(\Gamma_y(\varepsilon))\tag{G.1a}$$
equals one, so one choice of $\varepsilon$ makes every factor one. `degree_count` states this
consequence: there are such sets of programs that, for any singular and varying programs installed on
them, some choice of the varying bits makes both symbols one at every nonzero address.

The anchors and the balancing sets are hypotheses. The manuscript obtains them from a terminal of every
nonzero activation and an extra column at a terminal of activation $\alpha+\beta$, as [Lemma
7.12](../section-7/lemma-7-12-two-symbol-address.md) does; for one symbol on stationary terminals,
[Lemma 7.11](../section-7/lemma-7-11-one-symbol-address.md) takes any terminal as the anchor and the pair
itself as the balancing set. The zero-total packets of the proof are `final_family_graphs`: if two
symbols read separately surjective projections of one finite elementary alphabet, each with a minimum
nonempty unit seed of projected total label zero, then for every $b\ge1$ one compatible typed graph with
nonzero activations makes both symbols one at every nonzero address, every active configuration having
total label zero. The prime realization belongs to [Proposition G.7](proposition-g-7-final-stage.md).

The Lean statement differs from the print in four ways. The print requires the active data to satisfy
each prescribed filter at every nonzero address; this is not a hypothesis, since a symbol that vanishes
off its filter has a nonzero terminal polynomial only on its filter. The print adds that a
partitionability certificate suffices for the nonzero terminal polynomial; in Lean this is the separate
lemma `partitionable_terminalNonzero`. The order in which the stage and the prime representatives are
chosen is not part of the statement, which concerns typed graphs only. Both symbols read one alphabet in
`address_general`; symbols reading different projections of a common alphabet are handled in
`final_family_graphs`, where each symbol is composed with its projection (`mapType`), which preserves
the rules.

The reduction of Theorem 5.3 uses the two-symbol case, through `final_family_graphs` and Lemma 7.12, to
derive the address input of (3.9) from the field `PostLeaves.address` of [the remaining
hypotheses](../remaining-hypotheses.md). The one-symbol case does not enter the reduction: the cubes of
units behind (3.3b) are part of the field `PreLeaves.even_upper`, as on the page of Proposition 7.13.

**Proof sketch.** A network of primary auxiliaries acts on each symbol by an operator in the finite
differences of the pair bits; its constant term is $\det Q$ for the grounded Laplacian $Q$, and its
first-order coefficients are rooted-forest minors. A singular network for a target $x_*$ and a pair $e$
acts as $\partial_e$ plus higher terms at $x_*$ and as $1$ plus terms of positive degree elsewhere; the
two varying networks differ by $\partial_e$ plus higher terms at $x_*$ and only by terms of degree at
least two elsewhere. In (G.1a) any term of more than the minimum cost kills a terminal polynomial, and
the minimum-cost terms give, at each $x$, the coefficient of the chosen monomial, which is one.

## Depends on

- [Section 7: addresses and terminal polynomials](../section-7/README.md)
- [Lemma 7.6: the coefficient rules](../section-7/lemma-7-6-coefficient-rules.md)

## Proof depends on

- [Lemma 7.12: two symbols on one address family](../section-7/lemma-7-12-two-symbol-address.md)

## Sources

- [Appendix G](../../../sources/manuscript.md#appendix-g)
