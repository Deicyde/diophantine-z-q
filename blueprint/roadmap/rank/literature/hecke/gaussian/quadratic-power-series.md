---
article_id: af_85c7350516d8428c3fa3e07f
declaration: lemma
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.coeff_inv_quadratic, ZInQ.Contrib.HeckeFE.map_invOfUnit_one, ZInQ.Contrib.HeckeAll.coeff_twist_quadratic
---

# Inverses of quadratic power series

For a power series $\varphi$ with constant coefficient $1$, $\varphi^{-1}$ is its inverse in the
ring of formal power series, and $[T^k]$ takes the coefficient of $T^k$.

1. For complex $a,b$, the coefficients $\psi_k=[T^k]\,(1-aT+bT^2)^{-1}$ satisfy $\psi_0=1$,
   $\psi_1=a$ and $\psi_{k+2}=a\psi_{k+1}-b\psi_k$ for every $k\ge0$.
2. Let $f:R\to S$ be a homomorphism of commutative rings and $\varphi$ a power series over $R$ with
   constant coefficient $1$. Applying $f$ to the coefficients of $\varphi^{-1}$ gives the inverse
   of the series obtained by applying $f$ to the coefficients of $\varphi$.
3. For complex $\varepsilon,b,q$ with $\varepsilon^2=1$ and every $k\ge0$,
   $$[T^k]\,(1-\varepsilon bT+qT^2)^{-1}=\varepsilon^k\,[T^k]\,(1-bT+qT^2)^{-1}.$$

**Proof sketch.** (1) Compare coefficients in $(1-aT+bT^2)\cdot(1-aT+bT^2)^{-1}=1$.

(2) The image of $\varphi^{-1}$ is a left inverse of the image of $\varphi$, and the inverse of a
series with constant coefficient $1$ is unique.

(3) Induction on $k$, proving the statement for $k$ and $k+1$ together: both sides satisfy the
recursion of (1) with $a=\varepsilon b$, since $\varepsilon^{k+2}=\varepsilon^k$; the cases
$k=0,1$ are $\psi_0=1$ and $\psi_1=\varepsilon b$.

## Depends on

None.

## Sources

- [Deuring and the Hecke character](../../../../../sources/hecke-locators.md#deuring-and-the-hecke-character)
