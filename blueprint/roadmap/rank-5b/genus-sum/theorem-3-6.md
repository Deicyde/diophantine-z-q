---
article_id: af_a35b63122b55e1cf8db42104
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.det_M5b_eq_T5b, ZInQ.RouteK.Rank5b.Sec3.det_M5bG_eq_genusSum5b, ZInQ.RouteK.Rank5b.recip_bits, ZInQ.RouteK.Rank5b.sum_yBit_univ
---

# Row 5b of Smith's table (Theorem 3.6)

Let $n$ be squarefree with $n\equiv5\pmod8$. Then
$$\det M_{5b}=T_{5b}(n).$$
More generally, for bits $a,y,z$ on a finite set $V$ that satisfy reciprocity and $y(V)=0$, the
determinant of the matrix $M_{5b}$ built from the bits is the genus sum $T_{5b}$ of the bits.

Along the way: the bits of an odd number satisfy reciprocity, and for squarefree $n\equiv5\pmod8$ with
set of primes $P$, $y(P)=0$.

**Proof sketch.** Let the bits satisfy reciprocity and $y(V)=0$. In the forest form of
$\det M_{5b}$ the factor $1+y(V)$ is $1$, and grouping the forests by their root sets turns it into
$\sum_f\bigl(\sum_{k\in R}y_kz^{R\setminus k}\bigr)\mathrm{wt}(f)\prod_{\rho\in R}y(T_\rho)$ over all forests
$f$ on $V$, with $R$ the root set of $f$. This is the forest form of the genus sum, so
$\det M_{5b}=T_{5b}$.

For $n$, the bits of the primes of $n$ satisfy reciprocity, $a_{pq}+a_{qp}=y_py_q$, by quadratic
reciprocity. Since $n$ is squarefree, it is the product of its primes, so
$y(P)=\lambda(n)=\lambda(5)=0$. The matrix $M_{5b}$ of the bits is Smith's $M_{5b}$, and the genus sum
of the bits is $T_{5b}(n)$.

## Depends on

- [Smith's matrices $L$, $M_1$ and $M_{5b}$](../smith-matrices.md)
- [The genus sum $T_{5b}$](genus-sum.md)
- [The row-5b determinant as a forest sum](det-m5b-forests.md)

## Proof depends on

- [The genus sum as a forest sum](genus-sum-forests.md)
- [The genus sum of an odd number from its bits](genus-sum-bits.md)
- [Forests on a finite set](../forests/forests.md)

## Sources

- [Theorem 3.6](../../../sources/rank-5b-locators.md#theorem-36)
- [Row 5b of Smith's table](../../../sources/rank-5b-locators.md#row-5b-of-smiths-table)
- [Smith, Theorem 2.2 and row 5b of Table 2](../../../sources/rank-5b-locators.md#smith)
