---
article_id: af_b61dbe3690aadec998dbb373
declaration: abbrev
origin: background
statement: formalized
lean: ZInQ.Literature.cdLocal, ZInQ.Literature.cdLocal_eq, ZInQ.Literature.cdModel_baseChange, ZInQ.Literature.cdLocal_Δ_eq, ZInQ.Literature.cdLocal_c₄_eq, ZInQ.Literature.cdLocal_Δ_ne_zero, ZInQ.Literature.reduction_cdLocal
---

# The curve $C_d$ over a completion of $\mathbb Q$

For a finite place $v$ of $\mathbb Q$ and a natural number $d$, let $C_{d,v}$ be the curve
$C_d:y^2=x^3-d^2x$ over $\mathbb Q$ with its coefficients read in the completion $\mathbb Q_v$
(notation of [the places of $\mathbb Q$](completion.md)). Its basic facts:

1. $C_{d,v}$ is the [model $y^2=x^3-d^2x$](cd-model.md) over $\mathbb Q_v$, and it is the model
   $y^2=x^3-d^2x$ over $\mathcal O_v$ with its coefficients read in $\mathbb Q_v$. In particular it
   is integral.
2. $\Delta(C_{d,v})$ is the image in $\mathbb Q_v$ of the element $(2d)^6$ of $\mathcal O_v$, and
   $c_4(C_{d,v})$ is the image of $48d^2$.
3. If $d\ne0$, then $\Delta(C_{d,v})\ne0$.
4. If $C_{d,v}$ is minimal over $\mathcal O_v$, its reduction is the model $y^2=x^3-d^2x$ over
   $\kappa_v$.

**Proof sketch** (of the basic facts). (1) The model over a field is the short curve with
$A=-d^2$, and mapping the model over $\mathbb Q$, or over $\mathcal O_v$, into $\mathbb Q_v$ gives
the model over $\mathbb Q_v$. (2) The discriminant and $c_4$ commute with mapping the coefficients,
and the model over $\mathcal O_v$ has $\Delta=(2d)^6$ and $c_4=48d^2$. (3) $\mathbb Q_v$ has
characteristic $0$, so $2d\ne0$ there. (4) A minimal equation is reduced through its equation with
coefficients in $\mathcal O_v$, which here is the model over $\mathcal O_v$ (the map
$\mathcal O_v\to\mathbb Q_v$ is injective), and reducing the model over $\mathcal O_v$ gives the
model over $\kappa_v$.

## Depends on

- [The model $y^2=x^3-d^2x$ over a ring](cd-model.md)
- [The places of $\mathbb Q$ and their completions](completion.md)
- [Minimal Weierstrass equations over a discrete valuation ring](minimal-models.md)

## Sources

- [The L-series of the congruent number curves](../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
