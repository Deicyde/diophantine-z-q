---
article_id: af_d0af1128e738f1ed1f9a5e22
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.norm_gcd_eq, ZInQ.Contrib.HeckeFE.card_mul_fiber
---

# Factoring a Gaussian integer along coprime norms

Let $m,n>0$ be coprime natural numbers. Pairs and Gaussian integers are identified as in
[Gaussian integers as pairs](norm-fibres.md), and $\gcd$ in $\mathbb Z[i]$ is the greatest common
divisor computed by the Euclidean algorithm.

1. If $\gamma\in\mathbb Z[i]$ has norm $mn$, then $N(\gcd(\gamma,m))=m$.
2. For every $y\in A_{mn}$ there are exactly four pairs $(\alpha,\beta)\in A_m\times A_n$ with
   $\alpha\beta=y$.

**Proof sketch.** (1) Let $D=\gcd(\gamma,m)$ and $E=\gcd(\gamma,n)$. Since $D$ divides $m$ and
$\gamma$, $N(D)$ divides $m^2$ and $mn$, hence $m$ by coprimality; likewise $N(E)$ divides $n$.
Writing $D$ and $E$ as $\mathbb Z[i]$-combinations of $\gamma,m$ and of $\gamma,n$ and using
$mn=\gamma\bar\gamma$ shows $\gamma\mid DE$, so $mn\mid N(D)N(E)$. With $N(D)\le m$ and $N(E)\le n$
this forces $N(D)N(E)=mn$; if $N(D)<m$, then $N(D)N(E)<mn$.

(2) Let $D=\gcd(y,m)$, so $N(D)=m$ by (1), and $Q=y/D$, so $N(Q)=n$. For each unit $e$, the pair
$(eD,\bar eQ)$ is a solution, and distinct units give distinct solutions since $D\ne0$. Conversely,
if $\alpha\beta=y$ with $N(\alpha)=m$, then $\alpha\mid m$ (as $\alpha\bar\alpha=m$) and
$\alpha\mid y$, so $D=\alpha c$ with $N(c)=1$: $c$ is a unit, $\alpha=D\bar c$ and $\beta=cQ$.

## Depends on

- [Gaussian integers as pairs, norms and units](norm-fibres.md)

## Sources

- [Arithmetic of the Gaussian integers](../../../../../sources/hecke-locators.md#arithmetic-of-the-gaussian-integers)
