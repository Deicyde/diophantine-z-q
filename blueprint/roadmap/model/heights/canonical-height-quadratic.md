---
article_id: af_ff8211d1f91b2e16577a7a1f
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.canonHeight_parallelogram, ZInQ.canonHeight_zsmul
---

# The canonical height is quadratic

For all $P,Q\in C(K_0)$ and $m\in\mathbb Z$,
$$\widehat h(P+Q)+\widehat h(P-Q)=2\widehat h(P)+2\widehat h(Q),\qquad
\widehat h([m]P)=m^2\,\widehat h(P).$$

**Proof sketch.** (Silverman, Theorem VIII.9.3; Néron-Tate.) The naive height satisfies the
approximate parallelogram law: there is a constant $c$ with
$|h_x(P+Q)+h_x(P-Q)-2h_x(P)-2h_x(Q)|\le c$ for all $P,Q$ (Silverman, Theorem VIII.6.2).
Apply it to $[2^n]P,[2^n]Q$, divide by $4^n$ and let $n\to\infty$: since
$[2^n](P\pm Q)=[2^n]P\pm[2^n]Q$, the error $c/4^n$ tends to $0$ and the exact parallelogram law
follows. Taking $Q=P$ gives $\widehat h(O)=0$ and the case $m=2$; induction on $m\ge1$ with
$\widehat h((m+1)P)=2\widehat h(mP)+2\widehat h(P)-\widehat h((m-1)P)$ gives $m^2\widehat h(P)$, and
$\widehat h(-P)=\widehat h(P)$ gives negative $m$. The constant $c$ is not needed explicitly.

## Depends on

- [The canonical height on $C(K_0)$](canonical-height.md)

## Proof depends on

- [Basic properties of the canonical height](canonical-height-bounds.md)

## Sources

- [Height comparison](../../../sources/model-locators.md#height-comparison)
- [Silverman](../../../sources/model-locators.md#silverman)
