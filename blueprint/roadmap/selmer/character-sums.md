---
article_id: af_41be80ab1753669afb599a09
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Selmer.exists_xi, ZInQ.RouteK.Selmer.sum_quadraticChar_mul_sub, ZInQ.RouteK.Selmer.cubicCharSum, ZInQ.RouteK.Selmer.cubicCharSum_one_sq_le, ZInQ.RouteK.Selmer.cubicCharSum_sq_le, ZInQ.RouteK.Selmer.fibreCard, ZInQ.RouteK.Selmer.eight_mul_fibreCard_ge, ZInQ.RouteK.Selmer.exists_xi_of_card, ZInQ.RouteK.Selmer.xiCheckPrime, ZInQ.RouteK.Selmer.xiCheck_small
---

# A residue witness for the coverings over a finite field

Let $p$ be an odd prime and $d,a,b$ nonzero elements of $\mathbb F_p$. Then either $a$ and $b$ are
squares in $\mathbb F_p$, or there is $\xi\in\mathbb F_p$ such that $\xi/a$, $(\xi-d)/b$ and
$(\xi+d)/(ab)$ are squares (zero allowed).

Over any finite field $F$ of odd characteristic with $q$ elements and quadratic character
$\chi$, the proof uses:

- *(Lemma Q)* $\sum_\xi\chi((\xi-e)(\xi-e'))=-1$ for $e\ne e'$;
- *(Jacobsthal)* with $S(n)=\sum_\xi\chi(\xi^3-n\xi)$, $S(1)^2\le4q$, and $S(n)^2\le4q$ for every
  nonzero square $n$;
- *(the count)* for $d\ne0$ and signs $\alpha,\beta\in\{\pm1\}$, the number $N$ of
  $\xi\notin\{0,\pm d\}$ with $\chi(\xi)=\alpha$, $\chi(\xi-d)=\beta$, $\chi(\xi+d)=\alpha\beta$
  satisfies $8N\ge q-15-|S(d^2)|$; so $N\ge1$ once $q\ge26$.

**Proof sketch.** Lemma Q is the Jacobi sum $J(\chi,\chi^{-1})=-\chi(-1)$ after the substitution
$\xi=e+(e'-e)t$. Jacobsthal: $S(nt^2)=\chi(t)S(n)$, $S(0)=0$ and
$\sum_nS(n)^2=q(q-1)(1+\chi(-1))$ (by Lemma Q), which bounds $S(1)^2$ by $4q$. The count expands
$8N=\sum'(1+\alpha\chi(\xi))(1+\beta\chi(\xi-d))(1+\alpha\beta\chi(\xi+d))$: the constant term is
$q-3$, the linear and quadratic sums are bounded by Lemma Q, and the cubic term is $S(d^2)$. Since
$(q-15)^2>4q$ for $q\ge26$, $N\ge1$, and with $\alpha=\chi(a)$, $\beta=\chi(b)$ such a $\xi$ is the
witness. For the primes $3\le p\le23$ the statement is a finite check over all $d,a,b$, done by
the kernel.

## Depends on

None.

## Sources

- [Odd primes not dividing d](../../sources/selmer-locators.md#odd-primes-not-dividing-d)
