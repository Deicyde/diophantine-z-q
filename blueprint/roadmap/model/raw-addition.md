---
article_id: af_2f182a80de22918b605b23b5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.rel_rawAdd_iota
---

# Raw addition

For all $a,b\in\mathbb Z$ and every $R\in\mathbb Q^5$,
$$\operatorname{Add}_{\rm raw}(\iota(a),\iota(b),R)\iff R=\iota(a+b),$$
where $\operatorname{Add}_{\rm raw}(p,q,r)$ is $\mathrm{Rel}_{\mathtt{raw\_add}}(p,q,r)$: the polynomial of the raw
addition template vanishes at $(p,q,r)$ and some rational values of its six witnesses.
The branches of the template cover both identities, opposite points, distinct abscissas and
doubling with nonzero ordinate. The contract concerns canonical inputs only (with
$p=(1,0,0,0,0)$ the template accepts $R=q$ for every $q\in\mathbb Q^5$); every later use
supplies canonical input codes.

**Proof sketch.** $\iota(a)$ and $\iota(b)$ are the codes of $[a]P_0$ and $[b]P_0$, whose sum is
$[a+b]P_0$ with code $\iota(a+b)$; apply raw addition on canonical codes. No property of $P_0$
beyond lying on $E$ is used.

## Depends on

- [The raw addition template](../syntax/template-raw-add.md)
- [Point codes](point-codes.md)

## Proof depends on

- [Raw addition on canonical codes](raw-addition-points.md)
- [Elementary properties of codes](field/point-code-properties.md)

## Sources

- [Membership and addition](../../sources/model-locators.md#membership-and-addition)
