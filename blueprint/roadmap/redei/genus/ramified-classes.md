---
article_id: af_1579866d545d1c3ddc8f0152
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.psi_ones, ZInQ.RouteK.Redei.psi_single, ZInQ.RouteK.Redei.ambigClass_eq, ZInQ.RouteK.Redei.mk0_prod_ramIdeal
---

# The classes of the ramified primes

Let $n$ be odd and squarefree. Then $[\mathfrak p_p]^2=1$, so $c_p=[\mathfrak p_p]$, for every
$p\in T_n$; and $\psi$ sends the basis vector $\delta_p$ (equal to $1$ at $p$ and $0$ elsewhere)
to $[\mathfrak p_p]$. Let $e_n\in\mathbb F_2^{T_n}$ be $1$ at the primes dividing $n$ and $0$
elsewhere (that is, at $2$ when $n\equiv1\pmod4$), the exponent vector of $(\omega)$. Then
$$\psi(e_n)=1.$$
This uses the following, for every $n\ge1$: for every finite set $S$ of natural numbers, the
class of $\prod_{p\in S}\mathfrak p_p$ is $\prod_{p\in S}[\mathfrak p_p]$.

**Proof sketch.** $\mathfrak p_p^2=p\mathcal O$ is principal, so $[\mathfrak p_p]^2=1$ and
$c_p=[\mathfrak p_p]$; then $\psi(\delta_p)=c_p=[\mathfrak p_p]$. Since the class map is
multiplicative, $\psi(e_n)=\prod_{p\mid n}[\mathfrak p_p]=\bigl[\prod_{p\mid n}\mathfrak p_p\bigr]=[(\omega)]=1$.

## Depends on

- [The ambiguous class map $\psi$](ambiguous-class-map.md)

## Proof depends on

- [The primes of the discriminant ramify](../field/ramified-prime-ideals.md)
- [The ideal $(\sqrt{-n})$ is the product of the ramified odd primes](../field/ideal-of-omega.md)

## Sources

- [Step 3: ambiguous classes](../../../sources/redei-locators.md#step-3-ambiguous-classes)
