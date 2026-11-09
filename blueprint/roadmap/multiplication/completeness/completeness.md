---
article_id: af_fec789b921027a32697019ad
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.multiply_complete
---

# Completeness of the multiplication template

Assume pole completeness and the slope representation. For all $a,b\in\mathbb Z$,
$$\mathrm{Rel}_{\mathtt{multiply}}\bigl(\iota(a),\iota(b),\iota(ab)\bigr).$$

This direction does not use the six-contact estimate. Negative indices, zero indices and
coincident points need no separate treatment: every template is exact on canonical codes.

**Proof sketch.** Put $(n_1,n_2,n_3)=(a,b,ab)$. By the unfolding of the template it suffices to
show the unguarded certificate and the guard at $(\iota(n_1),\iota(n_2),\iota(n_3))$ with shift
points $\iota(c_*),\iota(c_*n_i)$. The guard holds at a true triple. For the height
certificate, write $x([n_i]P_0)=x_{i0}+x_{i1}s$ (zero if $n_i=0$), let $b_i\ge1$ be the least
common denominator of $x_{i0},x_{i1}$ and $a_{ij}=b_ix_{ij}\in\mathbb Z$. For each of the nine
integers $a_{10},a_{11},b_1,\dots,b_3$, the slope representation gives three good slopes with that
sum, and each of these $27$ slopes satisfies the slope predicate by
the completeness of the slope certificate. The semantics of the height certificate then
gives the relation.

## Depends on

- [The multiplication template](../../syntax/templates/template-multiply.md)
- [Point codes](../../model/point-codes.md)
- [Semantics of templates and recipes](../../syntax/template-semantics.md)
- [Pole completeness](../../main/pole-completeness.md)
- [The slope representation](slope-representation.md)

## Proof depends on

- [Unfolding the multiplication template](../certificate/multiply-unfolding.md)
- [Semantics of the height certificate template](../certificate/height-certificate-semantics.md)
- [The guard passes true triples and rejects false triples in the box](../certificate/guard-true-triples.md)
- [Completeness of the slope certificate for a true triple](slope-completeness.md)

## Sources

- [Choice of shifts](../../../sources/multiplication-locators.md#choice-of-shifts)
- [Conclusion of the multiplication proof](../../../sources/multiplication-locators.md#conclusion-of-the-multiplication-proof)
