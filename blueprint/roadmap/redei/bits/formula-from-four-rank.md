---
article_id: af_b934f3b403ab2295ab120815
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.redeiFormula_of_oddGClStatement, ZInQ.RouteK.Redei.gCl_dProd_eq_gBit
---

# Rédei's formula from the 4-rank statement

The 4-rank statement implies Rédei's formula. More precisely, assume the 4-rank statement. Then
for every odd $d$ and every nonempty set $B$ of primes of $d$,
$$g(d_B)\equiv g_d(B)\pmod2;$$
neither the squarefreeness of $d$ nor a condition on $d_B$ modulo $8$ is needed.

**Proof sketch.** The number $d_B$ is odd, squarefree and greater than $1$. By the 4-rank
statement, $g(d_B)$ is odd if and only if every vector killed by the Rédei matrix of $d_B$ is $0$
or $e_{d_B}$. That holds if and only if the kernel of $(L_B\mid z_B)$ is trivial for the bits of
$d$. These bits satisfy reciprocity because $d$ is odd, so the kernel is trivial if and only if
$g_d(B)=1$. Compare parities.

## Depends on

- [The 4-rank statement](../four-rank/four-rank-statement.md)
- [The statement of Rédei's formula](../redei-formula-statement.md)
- [The genus class number](../genus-class-number.md)
- [Rédei's $g$ from the bits](../../rank-5b/genus-sum/redei-g.md)
- [The genus sum $T_{5b}$](../../rank-5b/genus-sum/genus-sum.md)

## Proof depends on

- [The primes of $d_B$](primes-of-d-b.md)
- [The two kernel conditions agree](kernel-conditions.md)
- [Rédei's bit as the triviality of a kernel](kernel-and-g.md)
- [The kernel of $(L_B\mid z_B)$ through a square matrix](kernel-square-matrix.md)
- [Row 5b of Smith's table (Theorem 3.6)](../../rank-5b/genus-sum/theorem-3-6.md)

## Sources

- [Step 8: the bridge](../../../sources/redei-locators.md#step-8-the-bridge)
