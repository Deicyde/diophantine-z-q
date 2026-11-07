---
article_id: af_ffb01c564fad22b4e5a844c7
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.closedT_lt
---

# The cutoff is below a triple tower

With $D$ and $G_0$ as defined,
$$(96\cdot10^{13})^{13}\,D^{2210G_0^2D^3}<2^{D^8}<2^{2^{2^{9013}}} .$$
With the closed form of $T$ this is the bound on $T$ in the literal cutoff.

**Proof sketch.** Write $D$ symbolically and use $2^{2^{8008}}<D<2^{2^{9010}}$ and
$G_0<2^{37}$. First $(96\cdot10^{13})^{13}<2^{650}$ and $2210G_0^2<2^{86}<D$ (closed
comparisons), so $2210G_0^2D^3<D^4$. With $D<2^D$,
$D^{2210G_0^2D^3}<(2^D)^{D^4}=2^{D^5}$. Then $650+D^5<D^8$ since $D>650$, giving the first
inequality. Finally $D^8<\bigl(2^{2^{9010}}\bigr)^8=2^{2^{9013}}$, giving the second.

The manuscript's chain is $G_0<2^{37}$, $E_0<D^3$, $\log_2Q_D<D^5$, $\log_2A_{\rm ht}<D^7$ and
$\log_2T<D^8<2^{2^{9013}}$; the route above bounds the closed form directly and reaches the
same $\log_2T<D^8$.

## Depends on

- [The prescribed fixed constants](../../syntax/constants/fixed-constants.md)

## Proof depends on

- [Closed numerical comparisons](closed-comparisons.md)
- [Small explicit bounds](small-constant-bounds.md)
- [Bounds for $D$](d-bounds.md)

## Sources

- [Proof of Proposition 12.1, cutoff](../../../sources/size-locators.md#proof-of-proposition-121-cutoff)
- [Proposition 12.1](../../../sources/size-locators.md#proposition-121)
