---
article_id: af_d0988a1038d1d1b4a9d85b90
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Literature.isMinimal_baseChange_of_notMem, ZInQ.Literature.vK_u_eq_one, ZInQ.Literature.exists_reduction_variableChange
---

# Minimal Weierstrass equations over a discrete valuation ring

Let $R$ be a discrete valuation ring with maximal ideal $\mathfrak m$, residue field $\kappa$ and
fraction field $K$, and let $v:K\to\mathbb Z\cup\{\infty\}$ be its normalized valuation, so that
$v(x)\ge0$ exactly when $x\in R$. For a field $F$, a change of variables $C=(u,r,s,t)$ over $F$
($u\in F^\times$, $r,s,t\in F$) takes a Weierstrass equation $W$ over $F$ to the equation $C\cdot W$
obtained by the substitution $x=u^2x'+r$, $y=u^3y'+su^2x'+t$; then $\Delta(C\cdot
W)=u^{-12}\Delta(W)$ and $c_4(C\cdot W)=u^{-4}c_4(W)$. Below $F=K$ unless stated. The equation $W$
is *integral* if its coefficients lie in $R$, and *minimal* if it is integral and $v(\Delta(C\cdot
W))\ge v(\Delta(W))$ for every change of variables $C$ over $K$ with $C\cdot W$ integral. The
*reduction* $\tilde W$ of a minimal $W$ is the equation over $\kappa$ obtained by reducing its
coefficients modulo $\mathfrak m$.

1. If $W$ is a Weierstrass equation with coefficients in $R$ and $\Delta(W)\notin\mathfrak m^{12}$,
   then $W$, as an equation over $K$, is minimal.
2. Let $W$ be a Weierstrass equation over $K$ with $\Delta(W)\ne0$ and $C=(u,r,s,t)$ a change of
   variables over $K$. If $W$ and $C\cdot W$ are both minimal, then $v(u)=0$.
3. Let $W$ be a Weierstrass equation over $K$ and $C=(u,r,s,t)$ a change of variables over $K$
   such that $W$ and $C\cdot W$ are both minimal and $v(u)=0$. Then there is a change of variables
   $C'$ over $\kappa$ with $\widetilde{C\cdot W}=C'\cdot\tilde W$.

**Proof sketch.** (1) $W$ is integral. Let $C\cdot W$ be integral. If $v(u)\le0$, then
$v(\Delta(C\cdot W))=v(\Delta(W))-12v(u)\ge v(\Delta(W))$. If $v(u)>0$, then $u\in\mathfrak m$ and
$\delta=\Delta(C\cdot W)\in R$, so $\Delta(W)=u^{12}\delta\in\mathfrak m^{12}$, which is excluded.

(2) Minimality of $W$ applied to $C$, and of $C\cdot W$ applied to $C^{-1}$, gives
$v(\Delta(W))=v(\Delta(C\cdot W))=v(\Delta(W))-12v(u)$. Since $\Delta(W)\ne0$ its valuation is
finite, so $12v(u)=0$ and $v(u)=0$.

(3) $u$ is a unit of $R$. Between two integral equations, a change of variables whose $u$ is a unit
of $R$ has $r,s,t\in R$ as well (a standard fact), so it is a change of variables over $R$ between
the two equations with coefficients in $R$. Reducing $u,r,s,t$ modulo $\mathfrak m$ gives $C'$,
and reduction commutes with the substitution.

## Depends on

None.

## Sources

- [Minimal equations over a discrete valuation ring](../../../../sources/rank-locators.md#minimal-equations-over-a-discrete-valuation-ring)
