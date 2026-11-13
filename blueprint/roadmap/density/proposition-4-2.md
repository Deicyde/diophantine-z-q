---
article_id: af_54f42222e571b6052c2f2e07
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Density.uniformBadBound_holds, ZInQ.Density.uniformBadBound, ZInQ.Density.uniformGaussBadBound, ZInQ.Density.gaussBad_final_ineq
---

# The uniform bound holds

The uniform bad-prime bound holds. More precisely, there is $N_1$ such that for every $N\ge N_1$ and
every prime $\ell\equiv1\pmod4$ with $5\le\ell$ and $\ell^4\le N$,
$$\#\bigl(\mathrm{GB}_\ell\cap[0,N]\bigr)\le\frac{14402\,N}{\ell^2\log N},$$
and $\mathrm{Bad}_\ell\subseteq\mathrm{GB}_\ell$.

The research note proves the bound with $A_1=16003$ and $N_1=e^{1920}$; the Lean proof has
$A=14402$ and a threshold $N_1$ that is not explicit.

**Proof sketch.** Put $u=N^{1/40}$ and $w=\lfloor u\rfloor$, and apply the count of
$\mathrm{GB}_\ell$. Since $\sqrt N=u^{20}$, $K\le u^{20}/\ell$, and $\ell^4\le N$ gives $\ell\le u^{10}$.
The main term $20(2K+1)(2K+2)/\log w$ is then at most a constant times $N/(\ell^2\log N)$ (as
$\log N=40\log u$ and $\log w\ge\log(u-1)$), while the error terms $w+1$ and $2w^8(4K+4)$ are of order
$u^{28}$, which is at most $N/(\ell^2\log N)$ once $400\log u\le u^2$ and $u\ge4$. An elementary real
inequality collects the constants into $14402$.

## Depends on

- [The uniform bound for the primes bad at a medium $\ell$](uniform-bad-bound.md)

## Proof depends on

- [The count of primes $c^2+e^2$ with $\ell\mid c$ and $\ell\mid p+1$](gauss-bad-count.md)

## Sources

- [The sieve](../../sources/density-locators.md#the-sieve)
