---
article_id: af_41be80ab1753669afb599a09
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Selmer.sum_quadraticChar_mul_sub, ZInQ.RouteK.Selmer.cubicCharSum, ZInQ.RouteK.Selmer.cubicCharSum_one_sq_le, ZInQ.RouteK.Selmer.cubicCharSum_sq_le, ZInQ.RouteK.Selmer.cubicCharSum_mul_sq, ZInQ.RouteK.Selmer.cubicCharSum_zero, ZInQ.RouteK.Selmer.sum_cubicCharSum_sq, ZInQ.RouteK.Selmer.quadraticChar_pow_three, ZInQ.RouteK.Selmer.sum_quadraticChar_sub_sq, ZInQ.RouteK.Selmer.sum_quadraticChar_sq_sub, ZInQ.RouteK.Selmer.sum_quadraticChar_mul_sq_eq
---

# Cubic character sums over a finite field

Let $F$ be a finite field of odd characteristic with $q$ elements and quadratic character $\chi$, and put
$S(n)=\sum_{\xi\in F}\chi(\xi^3-n\xi)$. Then $\chi(a)^3=\chi(a)$ for every $a\in F$, and:

- *(Lemma Q)* $\sum_\xi\chi((\xi-e)(\xi-e'))=-1$ for $e\ne e'$, and $\sum_\xi\chi((\xi-e)^2)=q-1$;
- $S(nt^2)=\chi(t)S(n)$ for $t\ne0$, and $S(0)=0$;
- *(Jacobsthal)* $\sum_nS(n)^2=q(q-1)(1+\chi(-1))$; hence $S(1)^2\le4q$, and $S(n)^2\le4q$ for every
  nonzero square $n$.

**Proof sketch.** Lemma Q is the Jacobi sum $J(\chi,\chi^{-1})=-\chi(-1)$ after the substitution
$\xi=e+(e'-e)t$. Jacobsthal: $S(nt^2)=\chi(t)S(n)$, $S(0)=0$ and
$\sum_nS(n)^2=q(q-1)(1+\chi(-1))$ (by Lemma Q), which bounds $S(1)^2$ by $4q$.

## Depends on

None.

## Sources

- [Cubic character sums](../../sources/density-locators.md#cubic-character-sums)
