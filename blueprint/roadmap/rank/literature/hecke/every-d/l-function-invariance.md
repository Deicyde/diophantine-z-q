---
article_id: af_5a9aaa3c573b1cb01e49d69c
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeAll.not_hasMultiplicativeReduction_smul, ZInQ.Contrib.HeckeAll.hj_smul, ZInQ.Contrib.HeckeAll.localPolynomial_eq_ite, ZInQ.Contrib.HeckeAll.localPolynomial_smul
---

# The local polynomial is invariant under changes of variables when $j$ is integral

Let $R$ be a discrete valuation ring with fraction field $K$ and valuation $v$, and $W$ a
Weierstrass equation over $K$. Changes of variables $C$ (with scaling factor $u$), minimal
equations, reduction types and local polynomials are as in
[minimal Weierstrass equations](../../l-function-cd/minimal-models.md) and
[the local polynomial](../../l-function-cd/local-polynomial.md); the local polynomial of $W$ is
computed from the minimal equation chosen once and for all for $W$. Say that *$j$ is integral* for
$W$ if $3v(c_4(W))\ge v(\Delta(W))$.

1. If $j$ is integral for $W$, then for every change of variables $C$, the equation $C\cdot W$ does
   not have multiplicative reduction, and $j$ is integral for $C\cdot W$.
2. If $j$ is integral for $W$, the local polynomial of $W$ is
   $1-(q+1-\#\tilde W(\kappa))T+qT^2$ if the chosen minimal equation has good reduction, where $q$
   is the number of elements of the residue field $\kappa$ and $\tilde W(\kappa)$ is the set of
   points of the reduction of that equation (the number of elements of an infinite set read as
   $0$), and $1$ otherwise.
3. If $\Delta(W)\ne0$ and $j$ is integral for $W$, then $C\cdot W$ and $W$ have the same local
   polynomial for every change of variables $C$.

**Proof sketch.** (1) $c_4(C\cdot W)=u^{-4}c_4(W)$ and $\Delta(C\cdot W)=u^{-12}\Delta(W)$, so
integrality of $j$ is preserved. Multiplicative reduction of $C\cdot W$ would mean
$v(\Delta(C\cdot W))>0$ and $v(c_4(C\cdot W))=0$, whence
$v(\Delta(C\cdot W))\le3v(c_4(C\cdot W))=0$, a contradiction.

(2) By (1) the chosen minimal equation is not multiplicative, so of the four cases defining the
local polynomial only good reduction and the remaining case occur.

(3) Both local polynomials are given by (2). The chosen minimal equations of $W$ and of $C\cdot W$
differ by a change of variables $D$ whose scaling factor has $v=0$
([minimal Weierstrass equations](../../l-function-cd/minimal-models.md)), so their discriminants
have the same valuation and one has good reduction exactly when the other does. In the good case
their reductions differ by a change of variables over $\kappa$, which preserves the number of points
([point counts](../../l-function-cd/point-counts.md)).

## Depends on

- [Minimal Weierstrass equations over a discrete valuation ring](../../l-function-cd/minimal-models.md)
- [The local polynomial from any minimal equation](../../l-function-cd/local-polynomial.md)

## Proof depends on

- [Point counts under changes of variables and field isomorphisms](../../l-function-cd/point-counts.md)

## Sources

- [The curves for even and non-squarefree d](../../../../../sources/hecke-locators.md#the-curves-for-even-and-non-squarefree-d)
- [Minimal equations over a discrete valuation ring](../../../../../sources/rank-locators.md#minimal-equations-over-a-discrete-valuation-ring)
