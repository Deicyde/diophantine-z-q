---
article_id: af_88aafa62ac7a4d791a590032
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.PSide.jac, ZInQ.Contrib.PSide.jac_mul_sq, ZInQ.Contrib.PSide.jac_sq_mul_sq, ZInQ.Contrib.PSide.sum_char_mul_add, ZInQ.Contrib.PSide.sum_jac_sq, ZInQ.Contrib.PSide.sum_sq_le_two_mul, ZInQ.Contrib.PSide.jac_sq_le_four_mul
---

# Jacobsthal sums over a finite field and their bound

Let $F$ be a finite field with $q$ elements and $\chi$ its quadratic character, as in
[point counts by the quadratic character](quadratic-character-counts.md). For $a\in F$ the
*Jacobsthal sum* is the integer
$$\varphi(a)=\sum_{x\in F}\chi\bigl(x(x^2+a)\bigr).$$

1. For every $a\in F$ and $t\ne0$, $\varphi(at^2)=\chi(t)\,\varphi(a)$; hence
   $\varphi(at^2)^2=\varphi(a)^2$.

Suppose from now on that $F$ does not have characteristic $2$.

2. For $u,v\in F$,
   $$\sum_{a\in F}\chi\bigl((a+u)(a+v)\bigr)=\begin{cases}q-1 & \text{if } u=v,\\ -1 & \text{if } u\ne v.\end{cases}$$
3. $\displaystyle\sum_{a\in F}\varphi(a)^2=q(q-1)\bigl(1+\chi(-1)\bigr)$.
4. For every function $G:F\to\mathbb Z$ with $G\ge0$,
   $\sum_{t\in F}G(t^2)\le2\sum_{c\in F}G(c)$.
5. For every $a\ne0$, $\varphi(a)^2\le4q$.

Over $\mathbb F_p$ the scaling (1), the sums (2) and the second moment (3) are also
[character sums for the curves $y^2=x^3+ax$](../../../density/character-sums.md) (2), (3) and
[Jacobsthal's identity](../../../density/jacobsthal.md).

**Proof sketch.** (1) Substitute $x=ty$, a permutation of $F$:
$ty\bigl((ty)^2+at^2\bigr)=t^3\,y(y^2+a)$, and $\chi(t^3)=\chi(t)\chi(t^2)=\chi(t)$; square,
using $\chi(t)^2=1$. (2) If $u=v$, the substitution $b=a+u$ turns the sum into
$\sum_b\chi(b^2)$, which is $1$ for each of the $q-1$ nonzero $b$ and $0$ at $b=0$. If $u\ne v$,
put $w=u-v\ne0$ and substitute $a=wx-u$: then
$(a+u)(a+v)=-w^2\,x(1-x)$, so the sum is $\chi(-1)\sum_x\chi(x)\chi(1-x)$. This is $\chi(-1)$
times the Jacobi sum of $\chi$ with itself; $\chi$ is a nontrivial character equal to its own
inverse, so that Jacobi sum is $-\chi(-1)$, and the sum is $-\chi(-1)^2=-1$. (3) Expanding the
square and exchanging the sums,
$$\sum_a\varphi(a)^2=\sum_{x,y}\chi(xy)\sum_a\chi\bigl((a+x^2)(a+y^2)\bigr),$$
and by (2) the inner sum is $q-1$ if $x^2=y^2$, that is $y=\pm x$, and $-1$ otherwise. So the
summand is $q$ times $\chi(xy)$ if $y=\pm x$ and $0$ otherwise, minus $\chi(x)\chi(y)$; the second
part sums to $0$ since $\sum_x\chi(x)=0$. For $x\ne0$ the two values $y=x$ and $y=-x$ are distinct
(the characteristic is not $2$) and contribute $\chi(x^2)+\chi(-x^2)=1+\chi(-1)$; for $x=0$ the
contribution is $0$. Summing over the $q-1$ nonzero $x$ gives the claim. (4) Group the $t$ by
$c=t^2$: the left side is $\sum_c n_c\,G(c)$, where $n_c=1+\chi(c)\le2$ is the number of square roots
of $c$. (5) By (1), $\varphi(at^2)^2=\varphi(a)^2$ for each of the $q-1$ nonzero $t$, so
$$(q-1)\,\varphi(a)^2\le\sum_{t\in F}\varphi(at^2)^2\le2\sum_{c\in F}\varphi(ac)^2=2\sum_{c\in F}\varphi(c)^2,$$
by (4) with $G(c)=\varphi(ac)^2$ and then the permutation $c\mapsto ac$ of $F$ ($a\ne0$). By (3) and
$\chi(-1)\le1$, the right side is at most $4q(q-1)$. Divide by $q-1>0$.

## Depends on

- [Point counts by the quadratic character](quadratic-character-counts.md)

## Sources

- [Character sums](../../../../sources/density-locators.md#character-sums)
- [The Hasse bound for the congruent number curves](../../../../sources/rank-locators.md#the-hasse-bound-for-the-congruent-number-curves)
