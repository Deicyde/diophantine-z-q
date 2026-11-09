---
article_id: af_776e5a2d174ef37175301e95
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Config.base_card_sols', ZInQ.RouteK.Config.base_mem_sols', ZInQ.RouteK.Config.base_exists_first', ZInQ.RouteK.Config.base_isSol_iff, ZInQ.RouteK.Config.base_card_sols, ZInQ.RouteK.Config.baseSol₀_mem, ZInQ.RouteK.Config.base_exists_first
---

# The base configuration

Let $\mathcal C_0$ be a configuration on two symbols $\{p^*,q_0\}$ with $c_{p^*}=7$ and
$c_{q_0}=3$, and put $x=[q_0/p^*]$ (so $[p^*/q_0]=x+1$). Then the solutions of
$\Sigma(\mathcal C_0)$ are exactly the tuples with $a_0,u_{p^*},u_{q_0}$ free and, with
$w=u_{p^*}+u_{q_0}$,
$$v_{p^*}=a_0+xw,\quad v_{q_0}=a_0+(x+1)w,\quad a_1=0,\quad b_0=a_0,\quad b_1=u_{q_0}.$$
So $\Sigma(\mathcal C_0)$ has exactly $8$ solutions (dimension $3$), and for each $a_0\in\mathbb F_2$
it has the solution
$$\sigma_0:\quad u=(u_{p^*},u_{q_0})=(1,0),\quad v_{p^*}=a_0+x,\quad v_{q_0}=a_0+x+1,\quad
a_1=0,\quad b_0=a_0,\quad b_1=0,$$
whose first coordinate $(a_0,0,\mathbf 1_{p^*})$ is the class $(-1)^{a_0}p^*$.

**Proof sketch.** Here $\lambda=(1,1)$, $\mu=(0,1)$ and $c(\mathcal C_0)=21\equiv5$. Then
$(Ku)_{p^*}=xw$ and $(Ku)_{q_0}=(x+1)w$, and the rows are $xw+v_{p^*}=a_0$,
$(x+1)w+v_{q_0}=a_0$, $x(v_{p^*}+v_{q_0})+v_{p^*}=b_0$,
$u_{q_0}+(x+1)(v_{p^*}+v_{q_0})+v_{q_0}=b_0+b_1$, $a_0=b_0$, and the rows (D) for $c=5$:
$a_1=0$, $b_1=u_{q_0}$, $v_{p^*}+v_{q_0}=w$. The $\mathrm E1$ rows give $v_{p^*}$ and $v_{q_0}$,
hence $v_{p^*}+v_{q_0}=w$; substituting, the $\mathrm E2$ rows follow from (R) and
$b_1=u_{q_0}$. The equivalence is a finite check over the nine bits
$x,a_0,a_1,b_0,b_1,u_{p^*},u_{q_0},v_{p^*},v_{q_0}$, done by the kernel.

## Depends on

- [The Selmer system of a configuration](selmer-system.md)

## Sources

- [Base configuration](../../sources/route-k-locators.md#base-configuration)
