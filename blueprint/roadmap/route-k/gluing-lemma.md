---
article_id: af_a01dd9e54973f7b6bfda563d
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Config.Gluing.bijOn, ZInQ.RouteK.Config.Gluing, ZInQ.RouteK.Config.glue, ZInQ.RouteK.Config.glueMap, ZInQ.RouteK.Config.glueLift, ZInQ.RouteK.Config.Gluing.solsEquiv, ZInQ.RouteK.Config.Gluing.solsEquiv_symm_apply, ZInQ.RouteK.Config.Gluing.card_sols, ZInQ.RouteK.Config.glue_prodClass
---

# The gluing lemma

Let $\mathcal C$ be a configuration on $S=S'\sqcup\{g\}\sqcup G\sqcup R$, where
$R=\{r_\ell:\ell\in G\}$ consists of glue primes ($c_{r_\ell}=1$) with
$$[r_\ell/\ell]=[r_\ell/g]=1,\qquad[r_\ell/z]=0\text{ for every other }z\in S .$$
Put $X=G\cup\{g\}$. Let $\mathcal C^*$ be the configuration on $S'\sqcup\{g^*\}$ that agrees with
$\mathcal C$ on $S'$ and has
$$c_{g^*}=c_g\prod_{\ell\in G}c_\ell,\qquad[y/g^*]=\sum_{x\in X}[y/x],\qquad
[g^*/y]=\sum_{x\in X}[x/y]\qquad(y\in S');$$
it satisfies reciprocity because $\lambda$ is additive on odd classes, and
$c(\mathcal C^*)=c(\mathcal C)$. Then the map $\Phi$ that keeps $a_0,a_1,b_0,b_1$ and
$u|_{S'}$, $v|_{S'}$ and sends $u_g,v_g$ to $u_{g^*},v_{g^*}$ is a bijection from the solutions
of $\Sigma(\mathcal C)$ onto those of $\Sigma(\mathcal C^*)$. Its inverse sets $u_x=u_{g^*}$,
$v_x=v_{g^*}$ for $x\in X$ and, for $\ell\in G$,
$$\begin{aligned}
u_{r_\ell}&=\sum_{y\in S'}[y/\ell](u_y+u_{g^*})+u_{g^*}+\lambda_\ell(v_{g^*}+a_0),&&(2.1)\\
v_{r_\ell}&=\sum_{y\in S'}[y/\ell](v_y+v_{g^*})+v_{g^*}+\mu_\ell u_{g^*}+\lambda_\ell(v_{g^*}+b_0)+b_1\mu_\ell.&&(2.2)
\end{aligned}$$
In particular the two systems have the same number of solutions.

**Proof sketch.** (1) For $\ell\in G$ the row $\mathrm{E1}_{r_\ell}$ reads
$(u_\ell+u_{r_\ell})+(u_g+u_{r_\ell})=0$, so $u_\ell=u_g$; likewise $\mathrm{E2}_{r_\ell}$ gives
$v_\ell=v_g$. (2) At $y\in S'$ no glue prime is linked to $y$, and with $u$ constant on $X$ the
terms from $X$ in $(Ku)_y$ add up to $[g^*/y](u_g+u_y)$; so $\mathrm{E1}_y$, $\mathrm{E2}_y$ are
the rows of $\Sigma(\mathcal C^*)$. (3) The unknown $u_{r_\ell}$ occurs only in
$\mathrm{E1}_{r_\ell}$, $\mathrm{E1}_\ell$ and $\mathrm{E1}_g$; the row $\mathrm{E1}_\ell$
determines it, which is (2.1) (all solutions have $a_1=0$), and the sum
$\mathrm{E1}_g+\sum_\ell\mathrm{E1}_\ell$, in which the glue unknowns and the terms between two
elements of $X$ cancel, is the row $\mathrm{E1}_{g^*}$. The $\mathrm{E2}$ rows behave the same
way and give (2.2). (4) The product class is unchanged because $c_{r_\ell}=1$, and
$\lambda\cdot u=\lambda|_{S'}\cdot u|_{S'}+\lambda_{g^*}u_{g^*}$, and likewise for $\mu\cdot u$ and
$\lambda\cdot v$, so (D) and (R) agree. Hence $\Phi$ maps solutions to solutions; the formulas of
the inverse map solutions back, and the two maps are mutually inverse by step 1, (2.1) and
(2.2).

## Depends on

- [The Selmer system of a configuration](selmer-system.md)

## Sources

- [Partner and gluing lemmas](../../sources/route-k-locators.md#partner-and-gluing-lemmas)
