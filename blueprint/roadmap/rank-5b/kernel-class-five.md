---
article_id: af_7c9c0ad7b1088a602b98ef41
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Config.card_sols_eq, ZInQ.RouteK.Rank5b.Config.hEquivKer, ZInQ.RouteK.Rank5b.Config.solEquivTorsH, ZInQ.RouteK.Rank5b.Config.IsH, ZInQ.RouteK.Rank5b.Config.kvec, ZInQ.RouteK.Rank5b.Config.ofKer, ZInQ.RouteK.Rank5b.Config.M1c_mulVec_kvec, ZInQ.RouteK.Rank5b.Config.isH_ofKer, ZInQ.RouteK.Rank5b.Config.kvec_ofKer, ZInQ.RouteK.Rank5b.Config.ofKer_kvec, ZInQ.RouteK.Rank5b.Config.isSol_uadd_tors, ZInQ.RouteK.Rank5b.Config.torsCoord, ZInQ.RouteK.Rank5b.Config.isH_uadd_torsCoord, ZInQ.RouteK.Rank5b.tors, ZInQ.RouteK.Rank5b.uadd, ZInQ.RouteK.Rank5b.uadd_tors_tors, ZInQ.RouteK.Rank5b.Config.D_iff_of_five, ZInQ.RouteK.Rank5b.Config.sum_lam, ZInQ.RouteK.Rank5b.Config.sum_mu, ZInQ.RouteK.Rank5b.Config.lam_sum_of_five, ZInQ.RouteK.Rank5b.Config.mu_sum_of_five, ZInQ.RouteK.Rank5b.Config.bit_eq_bit_add, ZInQ.RouteK.Rank5b.Config.Lc_mulVec, ZInQ.RouteK.Rank5b.Config.LcT_mulVec, ZInQ.RouteK.Rank5b.Config.M1c_mulVec_inl, ZInQ.RouteK.Rank5b.Config.M1c_mulVec_inr, ZInQ.RouteK.Rank5b.Config.monsky_add, ZInQ.RouteK.Rank5b.Config.monsky_const, ZInQ.RouteK.Rank5b.Config.dot_add_right, ZInQ.RouteK.Rank5b.Config.dot_const, ZInQ.RouteK.Rank5b.Config.sum_monsky, ZInQ.RouteK.Rank5b.zmod2_mul_self
---

# The Selmer system of a class-5 configuration and the kernel of $M_1$

Let $\mathcal C$ be a configuration on $S$ of product class $c(\mathcal C)=5$, and let $M_1$ be
its matrix. For $e,f\in\mathbb F_2$ let $\tau_{e,f}$ be the tuple with $a_0=b_0=e$, $a_1=0$,
$b_1=f$, $u=f\mathbf 1$, $v=e\mathbf 1$ (for a number $n$, the class of $(-1,-n)^e(n,2)^f$). Let
$H$ be the set of solutions of $\Sigma(\mathcal C)$ with $b_1=0$ and $a_0=\lambda\cdot u$. Then:

1. adding $\tau_{e,f}$ coordinatewise maps solutions to solutions, and every solution is
   uniquely $h+\tau_{e,f}$ with $h\in H$, namely with $(e,f)=(a_0+\lambda\cdot u,\,b_1)$;
2. the map $h\mapsto(u+v,\,u)$ is a bijection from $H$ onto $\ker M_1$, with inverse
   $(s,t)\mapsto(u,v)=(t,s+t)$, $a_0=b_0=\lambda\cdot t$, $a_1=b_1=0$;
3. consequently $\Sigma(\mathcal C)$ has exactly $4\,|\ker M_1|$ solutions.

**Proof sketch.** For class $5$, $\sum_x\lambda_x=0$, $\sum_x\mu_x=1$, and the rows (D) read
$a_1=0$, $b_1=\mu\cdot u$, $\lambda\cdot v=\lambda\cdot u$. Monsky's matrix $K$ kills constant
vectors, so adding $\tau_{e,f}$ preserves every row, and it changes
$(a_0+\lambda\cdot u,\,b_1)$ by $(e,f)$; this gives 1. By reciprocity $(Ls)_x=(Ks)_x$ and
$(L^{\mathsf T}t)_x=(Kt)_x+\lambda_x(\lambda\cdot t+t_x)$, so $M_1(s,t)=0$ reads
$Kt+\lambda*(s+t)=(\lambda\cdot s+\lambda\cdot t)\lambda$ and $Ks+\mu*t=0$; summing the rows
gives $\lambda\cdot s=0$ and $\mu\cdot t=0$. With these, the rows E1, E2, (R) and (D) for the
tuple built from $(s,t)$ are the two kernel equations, and conversely; the two maps are inverse
on $H$ because $a_1=0$ and $a_0=b_0$ on solutions. Part 3 counts $4\cdot|H|$.

## Depends on

- [The Selmer system of a configuration](../route-k/selmer-system.md)
- [Smith's matrices $L$, $M_1$ and $M_{5b}$](smith-matrices.md)

## Sources

- [Lemma 4.1](../../sources/rank-5b-locators.md#lemma-41)
