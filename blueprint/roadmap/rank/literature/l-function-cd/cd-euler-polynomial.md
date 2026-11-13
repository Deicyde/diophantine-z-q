---
article_id: af_6c0a48a65b771e88d1586ffc
declaration: def
origin: background
statement: formalized
lean: ZInQ.Literature.cdEulerPoly, ZInQ.Literature.cdEulerPoly_coeff_zero
---

# The Euler polynomial of $C_d$ at $p$

For natural numbers $d$ and $p$, the *Euler polynomial* of $C_d$ at $p$ is the polynomial with
integer coefficients
$$P_{d,p}(T)=\begin{cases}1 & \text{if } p\mid2d,\\ 1-\bigl(p+1-N_d(p)\bigr)T+pT^2 & \text{if } p\nmid2d,\end{cases}$$
where $N_d(p)$ is the number of points of the [model $y^2=x^3-d^2x$](cd-model.md) over
$\mathbb Z/p\mathbb Z$: the point at infinity and the nonsingular solutions. Only prime $p$ is used
below; for a prime $p\nmid2d$, $N_d(p)=\#C_d(\mathbb F_p)$ is the number of points of $C_d$ over
$\mathbb F_p$, the point at infinity included. In every case the constant coefficient of
$P_{d,p}$ is $1$.

## Depends on

- [The model $y^2=x^3-d^2x$ over a ring](cd-model.md)

## Sources

- [The L-series of the congruent number curves](../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
