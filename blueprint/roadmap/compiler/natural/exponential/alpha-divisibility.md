---
article_id: af_e2b1c9dbd7c7d0a40a9428a5
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.AlphaPower.alphaZ_dvd_alphaZ_iff, ZInQ.AlphaPower.alphaZ_sq_dvd_alphaZ_iff
---

# Divisibility of alpha values

Let $b>2$ be a natural number and $U_n=\alpha_b(n)$.

1. For $k>0$ and every $m\in\mathbb N$: $U_k\mid U_m\iff k\mid m$.
2. (Equation (C.1)) For every $k\in\mathbb N$ and every $m>0$:
   $$U_k^2\mid U_m\iff kU_k\mid m .$$
   For $k=0$ both sides are false.

Divisibility is in $\mathbb Z$; all values involved are natural by the growth lemma.

**Proof sketch.** (1) Reducing $M^k$ modulo $U_k$ gives the scalar matrix $U_{k+1}I$ up to
the entry $-U_{k-1}\equiv U_{k+1}$ (from the recurrence $U_{k+1}+U_{k-1}=bU_k$), which is
invertible modulo $U_k$ by coprimality of adjacent terms. Equivalently, by the addition
formula $U_{k+n}=U_{k}U_{n+1}-U_{k-1}U_n$, so $U_k\mid U_{k+n}\iff U_k\mid U_n$ (as
$\gcd(U_k,U_{k-1})=1$). Removing periods of length $k$ reduces to $m<k$, where
$0\le U_m<U_k$ by strict growth, so $U_k\mid U_m$ iff $U_m=0$ iff $m=0$.
(2) For $k=0$: $U_0^2=0$ divides $U_m\ge m>0$ never, and $0\mid m$ never. For $k>0$, both
sides imply $k\mid m$ (the left by (1) since $U_k\mid U_m$); write $m=kq$ with $q\ge1$. From
$M^k\equiv U_kM-U_{k-1}I$ entrywise (the recurrence gives $M^k=U_kM-U_{k-1}I$ exactly),
$$M^{kq}=(U_kM-U_{k-1}I)^q\equiv(-U_{k-1})^qI+qU_k(-U_{k-1})^{q-1}M\pmod{U_k^2},$$
whose lower-left entry gives $U_m\equiv qU_k(-U_{k-1})^{q-1}\pmod{U_k^2}$. Since
$\gcd(U_k,U_{k-1})=1$, $U_k^2\mid U_m\iff U_k\mid q\iff kU_k\mid kq=m$; this includes
$U_k=1$.

## Depends on

- [The alpha sequence](alpha-sequence.md)

## Proof depends on

- [Matrix powers and the quadratic identity](alpha-matrix.md)
- [Growth of the alpha sequence](alpha-growth.md)

## Sources

- [Section 10.2 divisibility](../../../../sources/compiler-natural-locators.md#section-102-divisibility)
