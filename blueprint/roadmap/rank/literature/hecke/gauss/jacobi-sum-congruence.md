---
article_id: af_780130f589d4df53cbd301dc
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.GaussFE.chi_neg_one_mul_chi_two_sq, ZInQ.Contrib.GaussFE.two_add_two_i_dvd_jacobi_add_one
---

# The quartic Jacobi sum is $-1$ modulo $2+2i$

Let $p\equiv1\pmod4$ be prime, $\chi$ a multiplicative character of $\mathbb F_p$ with values in
$\mathbb Z[i]$ of order $4$ ([quartic characters](quartic-character.md)), and $J(\chi,\chi^2)$ the
[Jacobi sum](quartic-jacobi-sum.md).

1. $\chi(-1)\,\chi(2)^2=1$.
2. $2+2i$ divides $J(\chi,\chi^2)+1$ in $\mathbb Z[i]$.

**Proof sketch.** (1) As $p\equiv1\pmod4$, $-1=r^2$ for some $r\in\mathbb F_p$; then
$2r=(1+r)^2$ and $1+r\ne0$ (else $r=-1$ and $2=0$). So
$\chi(-1)\chi(2)^2=\chi(r)^2\chi(2)^2=\chi(2r)^2=\chi(1+r)^4=1$.

(2) Put $f(t)=\chi(t)\chi(1-t)^2$, so $J(\chi,\chi^2)=\sum_tf(t)$. Then $f(0)=f(1)=0$ and
$f(-1)=\chi(-1)\chi(2)^2=1$ by (1). Let $X=\mathbb F_p\setminus\{0,1,-1\}$, a set of $p-3$
elements. For $t\in X$: $f(t)^4=1$; $f(t^{-1})=f(t)$, from $1-t^{-1}=(-1)(1-t)t^{-1}$,
$\chi(t^{-1})=\chi(t)^3$ and $\chi(-1)^2=1$; and $t\mapsto t^{-1}$ maps $X$ to itself with no fixed
point, since $t^2=1$ forces $t=\pm1$. Pairing $t$ with $t^{-1}$, the sum $\sum_{t\in X}(f(t)-1)$ is
a sum of terms $2(f(t)-1)$, each divisible by $2+2i$ by
[quartic characters](quartic-character.md) (2). Finally, with $p-1=4k$,
$$J(\chi,\chi^2)+1=\sum_{t\in X}(f(t)-1)+(p-3)+2=\sum_{t\in X}(f(t)-1)+4k,$$
and $2+2i$ divides $4=(2+2i)(1-i)$.

## Depends on

- [Quartic characters of $\mathbb F_p$ with values in $\mathbb Z[i]$](quartic-character.md)
- [The point count of $y^2=x^3-x$ as a quartic Jacobi sum](quartic-jacobi-sum.md)

## Sources

- [Gauss and Jacobi sums](../../../../../sources/hecke-locators.md#gauss-and-jacobi-sums)
