---
article_id: af_ac3ae5e25cc122552bf8ad42
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.cataloguePrime, ZInQ.Syntax.catalogueProduct, ZInQ.Syntax.catalogueMax
---

# The prime catalogue

Let $W\ge1$, $k\ge0$ and $B\ge0$ be integers. For each residue $r$ with $1\le r<W$ and
$\gcd(r,W)=1$, let $p_{r,1}<p_{r,2}<\dots<p_{r,k}$ be the first $k$ primes $p$ with $p>B$ and
$p\equiv r\pmod W$. Define
$$\mathrm{catalogue\_product}(W,k,B)=\prod_{r}\prod_{j=1}^kp_{r,j},\qquad
\mathrm{catalogue\_max}(W,k,B)=\max_{r,j}p_{r,j},$$
with the maximum of an empty family equal to $0$. The fixed catalogue of the manuscript is
$W=4\prod_{p\le324}p$, $k=22$, $B=324$: the first twenty-two primes above $324$ in every unit
residue class modulo $W$. Its product is $H_{\rm cat}$ and its maximum $H_{\max}$.

The primes $p_{r,j}$ exist by Dirichlet's theorem on primes in arithmetic progressions.
The definition takes $p_{r,j}$ to be the $j$-th element, in increasing order, of the set of
primes $p>B$ with $p\equiv r\pmod W$; Dirichlet's theorem shows this set is infinite, so the
elements listed are the intended primes. Neither $H_{\rm cat}$ nor $H_{\max}$ is evaluated;
the catalogue bound hypothesis controls $H_{\max}$.

This is a definition.

## Depends on

None.

## Sources

- [Section 2.2](../../../sources/syntax-locators.md#section-22-catalogue-and-formal-multiple)
- [Appendix C.1](../../../sources/syntax-locators.md#appendix-c1-scalar-nodes)
