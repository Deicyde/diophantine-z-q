---
article_id: af_d68923104b2873d3c6b1d6ba
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.det_M5b_eq_one, ZInQ.RouteK.Rank5b.natAbs_classInt_zero, ZInQ.RouteK.Rank5b.lam8_prod_pow
---

# A first coordinate congruent to 7 forces $\det M_{5b}=1$ (Corollary 4.4)

Let $n>0$ be squarefree with $n\equiv5\pmod8$ and $|\mathrm{Sel}_2(C_n)|=8$. If some
$(a,b)\in\mathrm{Sel}_2(C_n)$ has $|a|\equiv7\pmod8$, then $\det M_{5b}=1$.

**Proof sketch.** Write $(a,b)$ as the pair of a solution of $\Sigma(\mathcal C_n)$ (Proposition 0).
For class $5$ the solution has $a_1=0$, so $|a|=\prod_pp^{u_p}$, and its class modulo $4$ gives
$y\cdot u=[\,|a|\equiv3\pmod4\,]=1$. The solution is not torsion: the torsion first coordinates
have absolute value $1$ or $n$, both $\equiv1\pmod4$. Theorem 4.3 gives $\det M_{5b}=y\cdot u=1$.

The note states the corollary for a first coordinate with odd part $\equiv3\pmod4$; the
statement here takes the shape $|a|\equiv7\pmod8$ of the hypothesis CR₃^Sel, a special case.

## Depends on

- [Smith's matrices $L$, $M_1$ and $M_{5b}$](smith-matrices.md)
- [Proposition 0](../selmer/proposition-0.md)

## Proof depends on

- [The rule of row 5b (Theorem 4.3)](theorem-4-3.md)

## Sources

- [Corollary 4.4](../../sources/rank-5b-locators.md#corollary-44)
