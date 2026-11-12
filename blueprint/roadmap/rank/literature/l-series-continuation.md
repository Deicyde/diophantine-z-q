---
article_id: af_04b3ac954449f43f53027579
declaration: def
origin: background
statement: formalized
lean: ZInQ.Literature.IsLContinuation, ZInQ.Literature.IsLContinuation.eq
---

# Entire continuations of the L-series of an elliptic curve

Let $E$ be a Weierstrass equation over $\mathbb Q$. For each prime $p$ let $f_p(T)$ be the local
polynomial of a minimal model of $E$ over $\mathbb Q_p$: $1-a_pT+pT^2$ with
$a_p=p+1-\#\tilde E(\mathbb F_p)$ (the points of the reduction, the point at infinity included) if
the reduction is good, $1-T$ if it is split multiplicative, $1+T$ if it is nonsplit
multiplicative, and $1$ if it is additive. The *L-series* of $E$ is the Dirichlet series
$$L(E,s)=\sum_{n\ge1}a_nn^{-s},$$
whose coefficients $a_n$ are those of the formal Euler product $\prod_pf_p(p^{-s})^{-1}$; its value
at $s$ is the sum of the series where the series converges absolutely, and $0$ elsewhere. The
recipe applies to every Weierstrass equation over $\mathbb Q$; the case that matters is an
elliptic curve, where the discriminant is nonzero.

A function $F:\mathbb C\to\mathbb C$ is an *entire continuation of $L(E,s)$* if $F$ is complex
differentiable on all of $\mathbb C$ and $F(s)=L(E,s)$ for every complex $s$ with
$\operatorname{Re}s>3/2$.

Two entire continuations of the same $L(E,s)$ are equal everywhere.

When $E$ is an elliptic curve, the series converges absolutely on the half-plane
$\operatorname{Re}s>3/2$, by Hasse's bound on $a_p$ (a standard fact, not proved here), so there $L(E,s)$ is the sum of the series. By the
uniqueness, a statement about the order of vanishing of an entire continuation at $s=1$ does not
depend on which continuation is chosen.

**Proof sketch** (of the uniqueness). Let $F$ and $G$ be entire continuations of $L(E,s)$. The
half-plane $\operatorname{Re}s>3/2$ is open and contains $2$, so $F$ and $G$ agree on a
neighbourhood of $2$. Both are complex differentiable on $\mathbb C$, hence analytic on the
connected set $\mathbb C$, and the identity theorem gives $F=G$.

## Depends on

None.

## Sources

- [The L-series of an elliptic curve](../../../sources/rank-locators.md#the-l-series-of-an-elliptic-curve)
- [Entire continuation](../../../sources/rank-locators.md#entire-continuation)
