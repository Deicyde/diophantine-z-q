---
article_id: af_edc1fa88263906cec6dcdfce
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Literature.localPolynomial_cdLocal_of_not_dvd, ZInQ.Literature.localPolynomial_cdLocal_of_dvd, ZInQ.Literature.localPolynomial_cdLocal_eq
---

# The local polynomial of $C_d$ at each prime

Let $v$ be a finite place of $\mathbb Q$ with prime $p=p_v$, $C_{d,v}$ the
[curve $C_d$ over $\mathbb Q_v$](cd-local.md), and $f_{C_{d,v}}$ its
[local polynomial](local-polynomial.md) over $\mathcal O_v$ (read off the minimal equation chosen
once and for all).

1. For every natural number $d$ with $p\nmid2d$,
   $$f_{C_{d,v}}(T)=1-\bigl(p+1-\#C_d(\mathbb F_p)\bigr)T+pT^2,$$
   where $\#C_d(\mathbb F_p)$ is the number of points of $y^2=x^3-d^2x$ over $\mathbb F_p$, the point
   at infinity included.
2. If $d$ is odd and squarefree and $p\mid2d$, then $f_{C_{d,v}}(T)=1$.
3. If $d$ is odd and squarefree, then $f_{C_{d,v}}=P_{d,p}$, the
   [Euler polynomial](cd-euler-polynomial.md) of $C_d$ at $p$, for every $v$.

**Proof sketch.** (1) By [minimality and reduction type](cd-reduction.md) (3), $C_{d,v}$ is minimal
with good reduction, so the local polynomial (3) gives
$1-(q+1-\#\tilde C_{d,v}(\kappa_v))T+qT^2$. Here $q=\#\kappa_v=p$ by
[the places of $\mathbb Q$](completion.md) (6), and the reduction has $\#C_d(\mathbb F_p)$ points by
minimality and reduction type (5). (2) By minimality and reduction type (4), $C_{d,v}$ is minimal
with additive reduction; $d$ is odd, so $d\ne0$ and $\Delta(C_{d,v})\ne0$
([the curve over $\mathbb Q_v$](cd-local.md) (3)); the local polynomial (2) gives $1$. (3) Split
on whether $p\mid2d$: (2) and (1) give the two cases of the definition of $P_{d,p}$.

## Depends on

- [The curve $C_d$ over a completion of $\mathbb Q$](cd-local.md)
- [The local polynomial from any minimal equation](local-polynomial.md)
- [The Euler polynomial of $C_d$ at $p$](cd-euler-polynomial.md)

## Proof depends on

- [Minimality and reduction type of $C_d$ at each prime](cd-reduction.md)
- [The places of $\mathbb Q$ and their completions](completion.md)

## Sources

- [The L-series of the congruent number curves](../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
- [The L-series of an elliptic curve](../../../../sources/rank-locators.md#the-l-series-of-an-elliptic-curve)
