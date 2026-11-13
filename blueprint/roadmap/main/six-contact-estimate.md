---
article_id: af_09e902abf5497930d0b6421d
declaration: def
origin: cited
statement: formalized
lean: ZInQ.SixContactEstimate
---

# The six-contact height estimate

Let $\mathcal C=\{0,-15,-20,-24,-30,-60\}$. For a finite set $S$ of primes containing
every prime at most $324$ and $u\in\mathbb Q\setminus\mathcal C$, let $M_S(u)$ be the
product of the primes $p\notin S$ for which $v_p(u-c)$ is positive and odd for some
$c\in\mathcal C$. Put $F_0=324!$, $D=F_0\,3^{256F_0^4}$, $G_0=116064000000$,
$E_0=10(DG_0)^2$, $Q_R=R^{RE_0}$, $B_{\rm cm}=D^2\,3^{21000D^2}+1$,
$C_{\rm cm}=2B_{\rm cm}+4096(1028+5D+84000D^2)$ and
$H_6(S;R)=2\cdot10^{13}\max(1,C_{\rm cm},Q_R^{17})$.

The six-contact estimate is the assertion that for every such $S$, every real
$R\ge\max(D,\max S,10^{12})$ and every $u\in\mathbb Q\setminus\mathcal C$,
$$h(u)\le H_6(S;R)\,M_S(u)^{24}.$$

Its proof needs Shimura curves, modularity and Arakelov geometry; here it is a hypothesis of the
main theorem.

## Depends on

None.

## Sources

- [Theorem 4.1](../../sources/manuscript.md#theorem-41)
