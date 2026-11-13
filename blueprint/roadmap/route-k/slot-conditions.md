---
article_id: af_5c458565dc4c2369ebc1c129
declaration: structure
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Slots, ZInQ.RouteK.Slots.sum_q₀_sym, ZInQ.RouteK.Slots.card_primes, ZInQ.RouteK.Slots.rev_q₀, ZInQ.RouteK.Slots.rev_rP, ZInQ.RouteK.Slots.rev_rT
---

# The slot conditions

Let $\beta,\theta$ be odd coprime integers, $P=P(\beta)$ and $T=P(\theta)$ their sets of primes,
$p_0\in P$, $G=P\setminus\{p_0\}$, $s=s(\beta)=[\beta<0]$ and $x=s+1\in\mathbb F_2$. *Slot data* for
$\beta,\theta,p_0$ are pairwise distinct primes $q_0$, $r_p$ ($p\in G$) and $r_\ell$ ($\ell\in T$),
none dividing $2\beta\theta$, such that:

- $q_0\equiv3\pmod8$, $[q_0/p]=1+\lambda_px$ for $p\in G$,
  $[q_0/p_0]=x+\sum_{p\in G}(1+\lambda_px)$, and $[q_0/\ell]=0$ for $\ell\in T$;
- for $p\in G$: $r_p\equiv1\pmod8$, $[r_p/p]=[r_p/p_0]=1$, and $[r_p/y]=0$ for every
  $y\in(P\setminus\{p,p_0\})\cup T\cup\{q_0\}$ and every $y=r_{p'}$ with $p'\in G\setminus\{p\}$;
- for $\ell\in T$: $r_\ell\equiv1\pmod8$, $[r_\ell/\ell]=[r_\ell/q_0]=1$, and $[r_\ell/y]=0$ for
  every $y\in P\cup(T\setminus\{\ell\})$, every $y=r_p$ with $p\in G$, and every $y=r_{\ell'}$ with
  $\ell'\in T\setminus\{\ell\}$.

For slot data, $\sum_{p\in P}[q_0/p]=x$; the slots number $|P|+|T|=\omega(\beta)+\omega(\theta)$;
and the reverse bits follow by reciprocity: $[y/r]=[r/y]$ for the glue slots $r\equiv1\pmod4$ and
$[y/q_0]=[q_0/y]+\lambda_y$ for every odd prime $y\ne q_0$.

The prime $q_0$ breaks the symmetry and forms the base configuration with the glued prime of
$\beta$; the $r_p$ glue the primes of $\beta$ into one virtual prime; the $r_\ell$ hang the primes
of $\theta$ on $q_0$. The condition $[q_0/\ell]=0$ is never used by the proof.

## Depends on

- [Residue bits](residue-bits.md)

## Proof depends on

- [Quadratic reciprocity in residue bits](reciprocity-bits.md)

## Sources

- [Slots](../../sources/route-k-locators.md#slots)
