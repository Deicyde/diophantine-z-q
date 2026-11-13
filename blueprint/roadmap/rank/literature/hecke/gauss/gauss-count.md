---
article_id: af_79461458a9d2b4fde3230b25
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.GaussFE.gauss_jacobi
---

# Gauss's theorem on the points of $y^2=x^3-x$

Let $p\equiv1\pmod4$ be prime. There are integers $A,B$ with
$$A^2+B^2=p,\qquad A\text{ odd},\qquad B\equiv A+1\pmod4,$$
such that
$$\#\{(x,y)\in\mathbb F_p^2:y^2=x^3-x\}=p+2A.$$
The congruences say that $-(A+Bi)\equiv1\pmod{2+2i}$.

**Proof sketch.** Take a character $\chi$ of order $4$
([quartic characters](quartic-character.md) (4)) and write $J(\chi,\chi^2)=A+Bi$.

*Norm.* $J\bar J=p$ ([the quartic Jacobi sum](quartic-jacobi-sum.md) (5)) gives $A^2+B^2=p$.

*Congruences.* By [the congruence](jacobi-sum-congruence.md) (2), $J+1=(2+2i)(c_1+c_2i)$ for some
integers $c_1,c_2$, so $A+1=2c_1-2c_2$ and $B=2c_1+2c_2$. Hence $A+1$ is even and
$B-A-1=4c_2$.

*Count.* By the quartic Jacobi sum (1), the count is
$p+\sum_x\left(\frac{x^3-x}p\right)$. By quartic characters (6), each term is $\chi(x^3-x)^2$, and
by the quartic Jacobi sum (3) and (4) the sum is $J+\bar J=2A$.

## Depends on

None.

## Proof depends on

- [Quartic characters of $\mathbb F_p$ with values in $\mathbb Z[i]$](quartic-character.md)
- [The point count of $y^2=x^3-x$ as a quartic Jacobi sum](quartic-jacobi-sum.md)
- [The quartic Jacobi sum is $-1$ modulo $2+2i$](jacobi-sum-congruence.md)

## Sources

- [The point count of Gauss](../../../../../sources/hecke-locators.md#the-point-count-of-gauss)
- [Gauss and Jacobi sums](../../../../../sources/hecke-locators.md#gauss-and-jacobi-sums)
