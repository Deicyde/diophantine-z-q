---
article_id: af_2840d1b42cede9e4039aa3b0
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.det_M5b_eq_dot, ZInQ.RouteK.Rank5b.Config.det_M5bc_eq, ZInQ.RouteK.Rank5b.Config.ofKer_zero, ZInQ.RouteK.Rank5b.Config.uadd_tors_zero_zero
---

# The rule of row 5b (Theorem 4.3)

Let $n>0$ be squarefree with $n\equiv5\pmod8$ and $|\mathrm{Sel}_2(C_n)|=8$. Let
$(a_0,a_1,b_0,b_1,u,v)$ be a tuple over the primes of $n$ whose pair $(a,b)$ lies in
$\mathrm{Sel}_2(C_n)$ and which is not one of the four torsion tuples $\tau_{e,f}$ (the classes of
$(-1,-n)^e(n,2)^f$). Then
$$\det M_{5b}=y\cdot u=\sum_{p\mid a}y_p ,$$
the parity of the number of primes $p\equiv3\pmod4$ dividing $a$.

**Proof sketch.** By Proposition 0 the tuple solves $\Sigma(\mathcal C_n)$, which has $8$
solutions, so by Lemma 4.1 $|\ker M_1|=2$. Subtracting from the tuple its torsion part
$\tau_{e,f}$ with $(e,f)=(a_0+y\cdot u,\,b_1)$ gives an element $h$ of $H$, and
$k=(u_h+v_h,\,u_h)$ is a nonzero element of $\ker M_1$ (it is nonzero because the tuple is not
torsion), so $\ker M_1=\{0,k\}$. $M_1$ is symmetric and $M_{5b}$ is $M_1$ bordered by $(0,y)$, so
Lemma 4.2 gives $\det M_{5b}=(0,y)\cdot k=y\cdot u_h$. Finally $u_h=u+f\mathbf 1$ and
$y\cdot\mathbf 1=0$ since $n\equiv1\pmod4$, so $y\cdot u_h=y\cdot u$. The proof does this for any
configuration of class $5$ whose system has $8$ solutions, and specializes to the configuration
of $n$.

## Depends on

- [Smith's matrices $L$, $M_1$ and $M_{5b}$](smith-matrices.md)
- [Proposition 0](../selmer/proposition-0.md)

## Proof depends on

- [The 2-Selmer group and the kernel of $M_1$ (Lemma 4.1)](lemma-4-1.md)
- [The Selmer system of a class-5 configuration and the kernel of $M_1$](kernel-class-five.md)
- [The bordered determinant (Lemma 4.2)](lemma-4-2.md)

## Sources

- [Theorem 4.3](../../sources/rank-5b-locators.md#theorem-43)
