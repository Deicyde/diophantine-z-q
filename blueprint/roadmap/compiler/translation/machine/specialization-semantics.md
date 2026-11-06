---
article_id: af_25a5543b3412621ee91b6258
declaration: theorem
origin: cited
---

# Semantics of the five-input specialization

For every $H\in\mathbb Z[X_0,\dots,X_{V-1}]$ with $V\ge2$, every $e_0\in\mathbb N$ and every
$\mathbf c\in\mathbb N^5$,
$$\exists\,\mathbf z\in\mathbb N^{V+2}:\ \operatorname{Spec}(H,e_0)(\mathbf c,\mathbf z)=0
\iff\exists\,\mathbf v\in\mathbb N^{V-2}:\ H\bigl(e_0,\operatorname{encode}_5(\mathbf c),\mathbf v\bigr)=0 .$$
For the universal halting polynomial ($V=1305804$) this reads: the natural precision
polynomial has a zero $(\mathbf c,\mathbf z)$ with $\mathbf z\in\mathbb N^{1305806}$ iff the universal
polynomial has a natural zero with program input $c_3$ and packed input
$\operatorname{encode}_5(\mathbf c)$.

**Proof sketch.** At natural arguments every summand of $\operatorname{Spec}(H,e_0)$ is the square of an
integer, so the sum vanishes iff each term does. The four pairing terms vanish iff
$z_5,\dots,z_8$ are the Cantor values, which forces $z_5=\operatorname{encode}_5(\mathbf c)$ and determines
$z_6,z_7,z_8$; the first term vanishes iff $H(e_0,z_5,z_9,\dots,z_{V+6})=0$. Take
$\mathbf v=(z_9,\dots,z_{V+6})$; conversely extend $\mathbf v$ by the four Cantor values.

## Depends on

- [The five-input specialization](five-input-specialization.md)
- [Cantor pairing and unpairing](cantor-unpairing.md)

## Sources

- [Section 10.3 specialization](../../../../sources/compiler-translation-locators.md#section-103-specialization)
- [Section 10.1 Cantor wrapper](../../../../sources/compiler-translation-locators.md#section-101-cantor-wrapper-and-acceptance)
