---
article_id: af_881ebcffd7a72ab296a11212
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.AlphaPower.alphaEqns_complete, ZInQ.AlphaPower.alphaEqns_iff
---

# Completeness of the alpha formula

For all natural numbers $b,N$ with $b>3$, the formula $\mathrm{Alpha}(\alpha_b(N),b,N)$
holds; that is, the fifteen conditions have natural witnesses with $X=\alpha_b(N)$. This
includes $N=X=0$.

Together with soundness: for natural $X,b,N$, $\mathrm{Alpha}(X,b,N)\iff(b>3\wedge
X=\alpha_b(N))$.

**Proof sketch.** Put $X=\alpha_b(N)\in\mathbb N$.

1. Choose $k>0$ with $u=\alpha_b(k)$ odd and $u>2X$ (odd alpha values are unbounded); put
   $t=\alpha_b(k+1)$, so $u^2+t^2=1+but$.
2. Put $m=ku>0$, $s=\alpha_b(m)$, $r=\alpha_b(m-1)$; then $r<s$ and $s^2+r^2=1+bsr$. By (C.1),
   $u^2\mid s$ because $ku\mid m$.
3. Put $v=bs-2r$; then $v\in\mathbb N$, $v+2r=bs$ and $v>2s$ (companion bound, $b>3$).
4. *Bounds.* $2X<u$ by choice; $s=\alpha_b(m)\ge\alpha_b(k)=u$ since $m\ge k$, so
   $2X<u\le s<v$; and $2N\le2\alpha_b(N)=2X<u$.
5. *Coprimality.* $\gcd(u,v)=1$: a common prime divisor $p$ is odd ($u$ is odd), divides $s$
   (as $u\mid s$) and hence $2r=bs-v$, hence $r$; but $r,s$ are adjacent alpha values,
   which are coprime.
6. *CRT.* With $u,v>0$ coprime, choose $w>2$ with $w\equiv2\pmod u$ and $w\equiv b\pmod v$.
7. Put $x=\alpha_w(N)$, $y=\alpha_w(N+1)$ (natural since $w\ge2$). Then $x^2+y^2=1+wxy$, and by
   parameter congruence $x\equiv\alpha_b(N)=X\pmod v$ and $x\equiv\alpha_2(N)=N\pmod u$.

All fifteen conditions hold.

## Depends on

- [The alpha formula](alpha-equations.md)
- [The alpha sequence](alpha-sequence.md)

## Proof depends on

- [Odd alpha values are unbounded](alpha-large-odd.md)
- [Divisibility of alpha values](alpha-divisibility.md)
- [Period and reflection modulo the companion](alpha-period.md)
- [Matrix powers and the quadratic identity](alpha-matrix.md)
- [Parameter congruence of the alpha sequence](alpha-parameter-congruence.md)
- [Growth of the alpha sequence](alpha-growth.md)
- [Soundness of the alpha formula](alpha-equations-sound.md)

## Sources

- [Section 10.2 alpha completeness](../../../../sources/compiler-natural-locators.md#section-102-alpha-completeness)
