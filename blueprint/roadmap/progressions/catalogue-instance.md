---
article_id: af_e33c13903b172075cd2ead63
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.catalogueBound8
---

# The catalogue bound holds

The catalogue bound holds: with $P_s=\prod_{p\le324}p$ and $W=4P_s$, for every integer $r$
with $0\le r<W$ and $\gcd(r,W)=1$, at least $22$ primes $p$ satisfy
$$324<p<2^{W^8}\qquad\text{and}\qquad p\equiv r\pmod W .$$

This replaces the explicit progression estimate of Bennett, Martin, O'Bryant and Rechnitzer
that the manuscript uses at the cutoff $2^{W^3}$; the larger cutoff $2^{W^8}$ is the range
of the effective Dirichlet theorem.

**Proof sketch.** By the small explicit bounds, $W>10^5>2^{16}$. The effective Dirichlet
theorem at $q=W$ and $a=r$ gives $22$ primes $p\equiv r\pmod W$ with $W^2<p<2^{W^8}$, and
$W^2>324$. Since $0\le r<W$, the congruence $p\equiv r\pmod W$ says that $p$ leaves the
remainder $r$ on division by $W$. The constant $W$ is never evaluated beyond these bounds.

## Depends on

- [The catalogue bound](../main/catalogue-bound.md)

## Proof depends on

- [An effective Dirichlet theorem](effective-dirichlet.md)
- [Small explicit bounds](../size/constants/small-constant-bounds.md)

## Sources

- [Proof of Proposition 12.1, catalogue](../../sources/size-locators.md#proof-of-proposition-121-catalogue)
- [Bennett-Martin-O'Bryant-Rechnitzer](../../sources/size-locators.md#bennett-martin-obryant-rechnitzer)
