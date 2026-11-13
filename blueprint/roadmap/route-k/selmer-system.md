---
article_id: af_05345694b5393db6bfc8d09c
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Config.IsSol, ZInQ.RouteK.Config.sols, ZInQ.RouteK.Unknowns, ZInQ.RouteK.Unknowns.first, ZInQ.RouteK.Config.monsky, ZInQ.RouteK.Config.E1, ZInQ.RouteK.Config.E2, ZInQ.RouteK.twoAdicRows, ZInQ.RouteK.Config.D, ZInQ.RouteK.dot
---

# The Selmer system of a configuration

Let $\mathcal C$ be a configuration on $S$. The *Selmer system* $\Sigma(\mathcal C)$ has the
unknowns $a_0,a_1,b_0,b_1\in\mathbb F_2$ and $u,v\in\mathbb F_2^S$. Write
$(Ku)_x=\sum_{y\ne x}[y/x](u_y+u_x)$ (Monsky's matrix) and
$\lambda\cdot u=\sum_x\lambda_xu_x$, and likewise $\mu\cdot u$, $\lambda\cdot v$. The equations
are
$$\begin{aligned}
(\mathrm{E1}_x)\quad&(Ku)_x+\lambda_xv_x=a_0\lambda_x+a_1\mu_x&&(x\in S),\\
(\mathrm{E2}_x)\quad&\mu_xu_x+(Kv)_x+\lambda_xv_x=b_0\lambda_x+b_1\mu_x&&(x\in S),\\
(\mathrm R)\quad&a_0=b_0,
\end{aligned}$$
and the two rows (D) for the product class $c=c(\mathcal C)$:

| $c$ | rows (D) |
| --- | --- |
| $1$ | $a_1=0$, $\mu\cdot u=0$, $\lambda\cdot v=\lambda\cdot u$ |
| $3$ | $a_1=0$, $b_0=\lambda\cdot v$, $b_1=\mu\cdot u$ |
| $5$ | $a_1=0$, $b_1=\mu\cdot u$, $\lambda\cdot v=\lambda\cdot u$ |
| $7$ | $a_1=0$, $\mu\cdot u=0$, $b_0=\lambda\cdot v$ |

Its solutions form a finite set (an $\mathbb F_2$-subspace); "dimension $3$" means exactly $8$
solutions. The *first coordinate* of a solution is $(a_0,a_1,u)$, standing for the class
$a=(-1)^{a_0}2^{a_1}\prod_xx^{u_x}$; the solution stands for the pair of classes $(a,b)$ with
$b=(-1)^{b_0}2^{b_1}\prod_xx^{v_x}$.

Every solution has $a_1=0$, and the system depends only on the classes and the off-diagonal
bits of $\mathcal C$.

For the configuration of an odd squarefree $d>0$, Proposition 0 (descent-alt §4.1) identifies
the solutions of $\Sigma(\mathcal C_d)$, through $(a,b)$, with the 2-Selmer group of
$C_d:y^2=x^3-d^2x$: the rows E1, E2 are the local conditions at the primes of $d$, (R) the
real place and (D) the place $2$. Proposition 0 is formalized in its own chapter
([Proposition 0](../selmer/proposition-0.md)); the descent of this chapter does not use it, and it
connects the system to rational points only through the
[certified rank hypothesis](../main/certified-rank.md) and its Selmer form.

## Depends on

- [Configurations](configuration.md)

## Sources

- [Configurations and the Selmer system](../../sources/route-k-locators.md#configurations-and-the-selmer-system)
- [Proposition 0](../../sources/route-k-locators.md#proposition-0)
