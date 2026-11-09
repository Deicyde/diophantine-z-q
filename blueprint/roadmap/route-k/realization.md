---
article_id: af_6474d83f09f1a7be5646d82b
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Slots.selmerCertified_d₁, ZInQ.RouteK.Slots.selmerCertified_d₂, ZInQ.RouteK.Inputs, ZInQ.RouteK.Slots.d₁, ZInQ.RouteK.Slots.d₂, ZInQ.RouteK.Slots.d₁_eq', ZInQ.RouteK.Slots.d₂_eq, ZInQ.RouteK.Slots.squarefree_d₁, ZInQ.RouteK.Slots.squarefree_d₂, ZInQ.RouteK.Slots.d₁_mod, ZInQ.RouteK.Slots.β_dvd_d₁, ZInQ.RouteK.selmerCertified_of_primeCfg
---

# The realization: both curves reduce to the base configuration

Let $\beta,\theta$ be integers such that $\beta$ is odd and squarefree with
$|\beta|\equiv7\pmod8$; $\theta>0$ is squarefree with $\theta\equiv1\pmod8$; $\beta$ and
$\theta$ are coprime; $[\beta/\ell]=0$ for every prime $\ell\mid\theta$; and $[\theta/p]=0$ for
every prime $p\mid\beta$. Let $p_0\in P(\beta)$, let $q_0$, $r_p$ ($p\in G=P(\beta)\setminus\{p_0\}$)
and $r_\ell$ ($\ell\in T=P(\theta)$) satisfy [the slot conditions](slot-conditions.md), and put
$$d_1=|\beta|\,q_0\prod_{p\in G}r_p\prod_{\ell\in T}r_\ell,\qquad d_2=d_1\theta .$$
Then $d_1$ and $d_2$ are squarefree, $d_1\equiv5\pmod8$, $\beta\mid d_1$, and both $(d_1,\beta)$
and $(d_2,\beta)$ carry Selmer certificates: $\Sigma(\mathcal C_{d_1})$ and
$\Sigma(\mathcal C_{d_2})$ have exactly $8$ solutions each, and each has a solution with first
coordinate the class of $\beta$. (So $d_2\equiv5\pmod8$ too.)

The hypotheses on $\beta,\theta$ are those that the multiplier lemma and (θ1)–(θ4) give for an
admissible input, in residue bits.

**Proof sketch.** Both numbers are products of distinct odd primes, so their configurations are
those of the families of their primes, and a solution of the family's system with first
coordinate $(s(\beta),0,[\,\cdot\mid\beta])$ is a certificate for the product. Let $s=s(\beta)$
and $x=s+1$.

*The first curve* ($d_1$, on $P\cup\{q_0\}\cup R_P\cup R_T$).
1. Each $r_\ell$ has exactly one nonzero bit inside this set, at its partner $q_0$; the partner
   lemma removes all of them and identifies $\Sigma(\mathcal C_{d_1})$ with
   $\Sigma(\mathcal C_\Sigma)$, $\mathcal C_\Sigma$ the configuration on
   $P\cup\{q_0\}\cup R_P$.
2. The gluing lemma applies to $\mathcal C_\Sigma$ with $g=p_0$, $G=P\setminus\{p_0\}$, glue
   primes $r_p$ and $S'=\{q_0\}$. The glued configuration lives on $\{p^*,q_0\}$ with
   $c_{p^*}=|\beta|\bmod8=7$, $c_{q_0}=3$ and $[q_0/p^*]=\sum_{p\in P}[q_0/p]=x$.
3. By the base configuration lemma it has $8$ solutions; hence so do $\Sigma(\mathcal C_\Sigma)$
   and $\Sigma(\mathcal C_{d_1})$.
4. Lift the solution $\sigma_0$ with $a_0=s$: through the gluing lemma, $u_P=\mathbf 1_P$,
   $u_{q_0}=0$, and by (2.1) $u_{r_p}=[q_0/p]+1+\lambda_px=0$ by the choice of $[q_0/p]$; through
   the partner lemma, $u_{r_\ell}=u_{q_0}=0$. The first coordinate is $(s,0,\mathbf 1_P)$, the class
   of $\beta$.

*The second curve* ($d_2$, on $P\cup R_P\cup\{q_0\}\cup T\cup R_T$).
5. The gluing lemma applies with $g=q_0$, $G=T$, glue primes $r_\ell$ and $S'=P\cup R_P$. The glued
   vertex has class $q_0\theta\equiv3\pmod8$ by (θ1). For $p\in P$,
   $\sum_{\ell\in T}[\ell/p]=[\theta/p]=0$, because $\theta=\prod_{\ell\in T}\ell$; and
   $\sum_{\ell\in T}[p/\ell]=[\theta/p]+\lambda_p\sum_{\ell\in T}\lambda_\ell=0$ by reciprocity prime by
   prime, since $\sum_\ell\lambda_\ell=\lambda(\theta)=0$. The bits between $R_P$ and $T$ vanish by
   construction. So the glued configuration is $\mathcal C_\Sigma$ with $q_0^*$ in place of $q_0$,
   and $\Sigma(\mathcal C_{d_2})$ has $8$ solutions by steps 1–3.
6. Lift the solution of step 4 through this gluing: $u_T=u_{q_0}=0$, $v_{q_0}=s+x+1=0$, and by
   (2.1), for $\ell\in T$,
   $u_{r_\ell}=\sum_{p\in P}[p/\ell]+\lambda_\ell s=[|\beta|/\ell]+\lambda_\ell s
   =([\beta/\ell]+s\lambda_\ell)+s\lambda_\ell=0$, using $[\beta/\ell]=0$. The first coordinate is
   again the class of $\beta$.

## Depends on

- [The slot conditions](slot-conditions.md)
- [The configuration of an odd number and Selmer certificates](prime-configuration.md)

## Proof depends on

- [The partner lemma](partner-lemma.md)
- [The gluing lemma](gluing-lemma.md)
- [The base configuration](base-configuration.md)
- [Quadratic reciprocity in residue bits](reciprocity-bits.md)

## Sources

- [Proof of the descent lemma](../../sources/route-k-locators.md#proof-of-the-descent-lemma)
