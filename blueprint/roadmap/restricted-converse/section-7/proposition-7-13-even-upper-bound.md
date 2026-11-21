---
article_id: af_fe72b2de76c3a7574c525947
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Wiring.evenUpper33b_of_RC11Inputs, ZInQ.Manuscript.RC.Wiring.EvenUpper33b, ZInQ.Manuscript.RC.Wiring.EvenUpperRC11Inputs
---

# Proposition 7.13: the partitionable even upper bound (3.3b)

Assume [the cited results](../printed-results.md) and the field `PreLeaves.even_upper` of [the remaining
hypotheses](../remaining-hypotheses.md) (ELLIOT), which asks for: a set of units of the even symbol at
which [(3.3a)](equation-3-3a-unit-symbol-bound.md) holds with some $C_0$; [(3.2)](proposition-7-2-even-scalar.md)
for the normalization of $L_*$ at some level $N_0$; and, for every partitionable $d\ne0$ with
$\operatorname{corank}_{\mathbb Z_2}\mathrm{Sel}_{2^\infty}(E^{(d)}/\mathbb Q)=0$ and every $b$, an
admissible binary family of dimension at least $b$ based at $d$ whose members at the nonzero addresses
are units. Assume also that $L_*$ is the normalization of Proposition 7.2 and that $L_*(h)\ne0$ exactly
when $L(E^{(h)},1)\ne0$. Let $\ell>0$. Then there is $C_1$ such that every partitionable $d\ne0$ with
$\operatorname{corank}_{\mathbb Z_2}\mathrm{Sel}_{2^\infty}(E^{(d)}/\mathbb Q)=0$ satisfies
$$v_2L_*(d)\le2\omega(d)+s(d)+C_1.\tag{3.3b}$$

The Lean statement records only the valuation bound, not $L_*(d)\ne0$. The function $L_*$ and the
predicate "partitionable" are interface data of the remaining hypotheses, constrained only by their
fields. The cubes of units, which the manuscript builds with [Lemma 7.9](lemma-7-9-minimum-seeds.md)
and [Lemma 7.11](lemma-7-11-one-symbol-address.md), are part of the leaf field rather than derived.

**Proof sketch.** Fix a partitionable $d$ of corank zero and take one cube of units based at $d$, of
dimension larger than the bounded Boolean bit degrees of the scalar's sign-evaluation coefficient.
The scalar of (3.2) has one uniformly cleared denominator on the cube, so at a precision beyond the
nonzero-address bound and the clearing exponent some nonzero address is congruent to the base. If
$v_2L_*(d)$ exceeded the bound, the corank-zero comparison in (3.2) would force the same at that
address, contradicting (3.3a) there. Nonvanishing at the units gives corank zero by the forward
rank-zero theorem.

## Depends on

- [The cited results](../printed-results.md)
- [The remaining hypotheses](../remaining-hypotheses.md)
- [Section 7: unit seeds and partitionable lists](README.md)

## Proof depends on

- [Proposition 7.2: the fixed-form even scalar (3.2)](proposition-7-2-even-scalar.md)
- [(3.3a): the bound at a unit of the even symbol](equation-3-3a-unit-symbol-bound.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
