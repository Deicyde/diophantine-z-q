---
article_id: af_ff8d06cb95cda44e44c2a4bd
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Config.Partner.bijOn, ZInQ.RouteK.Config.Partner, ZInQ.RouteK.Config.erase, ZInQ.RouteK.Config.Partner.isSol_iff, ZInQ.RouteK.Config.Partner.solsEquiv, ZInQ.RouteK.Config.Partner.solsEquiv_symm_apply, ZInQ.RouteK.Config.Partner.card_sols, ZInQ.RouteK.Config.Partners, ZInQ.RouteK.Config.restrictLeft, ZInQ.RouteK.Config.Partners.isSol_iff, ZInQ.RouteK.Config.Partners.bijOn, ZInQ.RouteK.Config.Partners.card_sols
---

# The partner lemma

Let $\mathcal C$ be a configuration on $S$, let $r\in S$ be a glue prime ($c_r=1$), and let
$y\in S\setminus\{r\}$ be its *partner*: $[r/y]=1$ and $[r/z]=0$ for every
$z\notin\{r,y\}$. Let $\mathcal C\setminus r$ be the restriction of $\mathcal C$ to
$S\setminus\{r\}$. Then a tuple $(a_0,a_1,b_0,b_1,u,v)$ solves $\Sigma(\mathcal C)$ if and only
if $u_r=u_y$, $v_r=v_y$ and its restriction to $S\setminus\{r\}$ solves
$\Sigma(\mathcal C\setminus r)$. Consequently forgetting $u_r,v_r$ is a bijection from the
solutions of $\Sigma(\mathcal C)$ onto those of $\Sigma(\mathcal C\setminus r)$; it keeps
$a_0,a_1,b_0,b_1$, and its inverse sets $u_r=u_y$, $v_r=v_y$. In particular the two systems have
the same number of solutions.

The same holds for a family: if $S=S_0\sqcup R$ where every $r\in R$ is a glue prime with a
partner $y(r)\in S_0$ and $[r/z]=0$ for every $z\notin\{r,y(r)\}$ (other elements of $R$
included), then restriction to $S_0$ is a bijection from the solutions of $\Sigma(\mathcal C)$
onto those of $\Sigma(\mathcal C|_{S_0})$, inverted by $u_r=u_{y(r)}$, $v_r=v_{y(r)}$.

**Proof sketch.** Since $c_r=1$, $\lambda_r=\mu_r=0$ and $[z/r]=[r/z]$, so $\mathrm{E1}_r$ reads
$[y/r](u_y+u_r)=u_y+u_r=0$ and $\mathrm{E2}_r$ reads $v_y+v_r=0$. The unknowns $u_r,v_r$ occur
elsewhere only in $\mathrm{E1}_y$, $\mathrm{E2}_y$, through the terms $[r/y](u_r+u_y)$ and
$[r/y](v_r+v_y)$, which vanish once $\mathrm{E1}_r$, $\mathrm{E2}_r$ hold; every other row is the
corresponding row of $\Sigma(\mathcal C\setminus r)$. The product class does not change because
$c_r=1$, and $r$ contributes nothing to $\lambda\cdot u$, $\mu\cdot u$, $\lambda\cdot v$, so the
rows (D) and (R) agree. The single-prime statement is the family statement with $R=\{r\}$, after
reindexing.

## Depends on

- [The Selmer system of a configuration](selmer-system.md)

## Sources

- [Partner and gluing lemmas](../../sources/route-k-locators.md#partner-and-gluing-lemmas)
