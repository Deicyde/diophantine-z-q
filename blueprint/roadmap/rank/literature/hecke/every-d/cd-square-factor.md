---
article_id: af_fd9ca2ed87656641014269f6
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeAll.hj_cdLocal, ZInQ.Contrib.HeckeAll.scaleChange, ZInQ.Contrib.HeckeAll.scaleChange_smul, ZInQ.Contrib.HeckeAll.LFunction_cd_sq_mul, ZInQ.Contrib.HeckeAll.LSeries_cd_sq_mul
---

# $L(C_{m^2d},s)=L(C_d,s)$

For a natural number $m\ne0$, the *scaling* by $m$ is the change of variables over $\mathbb Q$ with
$u=m$ and $r=s=t=0$, that is $(x,y)\mapsto(x/m^2,y/m^3)$. Notation of
[the curve $C_d$ over $\mathbb Q_v$](../../l-function-cd/cd-local.md) and
[invariance of the local polynomial](l-function-invariance.md); $a_n(E)$ and $L(E,s)$ are as in
[entire continuations](../../l-series-continuation.md).

1. For every finite place $v$ and every natural number $d$, $j$ is integral for $C_{d,v}$:
   $3v(c_4)\ge v(\Delta)$.
2. For natural numbers $d$ and $m\ne0$, the scaling by $m$ carries $y^2=x^3-(m^2d)^2x$ to
   $y^2=x^3-d^2x$.
3. If $d\ne0$ and $m\ne0$, then $a_n(C_{m^2d})=a_n(C_d)$ for every $n$, and
   $L(C_{m^2d},s)=L(C_d,s)$ for every complex $s$.

**Proof sketch.** (1) $c_4^3=(48d^2)^3=1728\,(2d)^6=1728\,\Delta$, and $1728$ is integral.

(2) The scaling divides $a_4$ by $m^4$: $-(m^2d)^2/m^4=-d^2$.

(3) The coefficients of an L-series are built from the local polynomials at the finite places.
Over $\mathbb Q_v$, $C_d$ is the scaling of $C_{m^2d}$ by (2), $C_{m^2d,v}$ has nonzero discriminant
as $m^2d\ne0$, and $j$ is integral for it by (1); so the two local polynomials agree
([invariance of the local polynomial](l-function-invariance.md) (3)). Equal coefficients give equal
L-series.

## Depends on

- [The curve $C_d$ over a completion of $\mathbb Q$](../../l-function-cd/cd-local.md)
- [The local polynomial is invariant under changes of variables when $j$ is integral](l-function-invariance.md)
- [Entire continuations of the L-series of an elliptic curve](../../l-series-continuation.md)

## Sources

- [The curves for even and non-squarefree d](../../../../../sources/hecke-locators.md#the-curves-for-even-and-non-squarefree-d)
