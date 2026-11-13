---
article_id: af_103219095807f3ad77bc6f10
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Literature.vK_minimal_Δ, ZInQ.Literature.vK_minimal_c₄, ZInQ.Literature.localPolynomial_of_hasAdditiveReduction, ZInQ.Literature.natCard_point_reduction_minimal, ZInQ.Literature.localPolynomial_of_hasGoodReduction
---

# The local polynomial from any minimal equation

Let $R$, $\mathfrak m$, $\kappa$, $K$ and $v$ be as in
[minimal Weierstrass equations](minimal-models.md), and let $q$ be the number of elements of
$\kappa$ ($0$ if $\kappa$ is infinite). A minimal equation $W$ has *good reduction* if
$v(\Delta(W))=0$, *multiplicative reduction* if $v(\Delta(W))>0$ and $v(c_4(W))=0$ (split or
nonsplit according as the slopes of the tangents at the node lie in $\kappa$ or not), and *additive
reduction* if $v(\Delta(W))>0$ and $v(c_4(W))>0$.

Every Weierstrass equation $W$ over $K$ has a minimal equation of the form $C_0\cdot W$; fix one,
$W^{\min}$, chosen once and for all. The *local polynomial* of $W$ is
$$f_W(T)=\begin{cases}1-aT+qT^2,\quad a=q+1-\#\tilde W^{\min}(\kappa), & \text{if $W^{\min}$ has good reduction},\\ 1-T & \text{if $W^{\min}$ has split multiplicative reduction},\\ 1+T & \text{if $W^{\min}$ has nonsplit multiplicative reduction},\\ 1 & \text{otherwise},\end{cases}$$
where $\#\tilde W^{\min}(\kappa)$ is the number of points of the reduction over $\kappa$, the point
at infinity included.

Now let $W$ be a Weierstrass equation over $K$ that is itself minimal.

1. If $\Delta(W)\ne0$, then $v(\Delta(W^{\min}))=v(\Delta(W))$ and
   $v(c_4(W^{\min}))=v(c_4(W))$.
2. If $\Delta(W)\ne0$ and $W$ has additive reduction, then $f_W(T)=1$.
3. If $W$ has good reduction, then $\#\tilde W^{\min}(\kappa)=\#\tilde W(\kappa)$ and
   $$f_W(T)=1-\bigl(q+1-\#\tilde W(\kappa)\bigr)T+qT^2 .$$

So at a place of good reduction, or of additive reduction with nonzero discriminant, the local
polynomial can be read off any minimal equation, not only the chosen one.

**Proof sketch.** (1) $W^{\min}=C_0\cdot W$ with $W$ and $C_0\cdot W$ both minimal, so by
[minimal Weierstrass equations](minimal-models.md) (2) the $u$ of $C_0$ has $v(u)=0$; since
$\Delta$ and $c_4$ are multiplied by $u^{-12}$ and $u^{-4}$, their valuations do not change.
(2) By (1), $v(\Delta(W^{\min}))>0$ and $v(c_4(W^{\min}))>0$, so $W^{\min}$ has neither good nor
multiplicative (split or nonsplit) reduction, and $f_W=1$. (3) Good reduction gives
$\Delta(W)\ne0$, so by (1) $W^{\min}$ has good reduction as well. By minimal Weierstrass equations
(2) and (3) there is a change of variables $C'$ over $\kappa$ with
$\tilde W^{\min}=C'\cdot\tilde W$. The reduction $\tilde W$ has nonzero discriminant, since $W$ has
good reduction, so by [point counts](point-counts.md) (4) the two reductions have the same number of
points, and the first case of the definition gives the formula.

## Depends on

- [Minimal Weierstrass equations over a discrete valuation ring](minimal-models.md)

## Proof depends on

- [Point counts under changes of variables and field isomorphisms](point-counts.md)

## Sources

- [Minimal equations over a discrete valuation ring](../../../../sources/rank-locators.md#minimal-equations-over-a-discrete-valuation-ring)
- [The L-series of an elliptic curve](../../../../sources/rank-locators.md#the-l-series-of-an-elliptic-curve)
