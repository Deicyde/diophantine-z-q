---
article_id: af_ad256a291ee0bbf3ce207f51
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Density.sum_card_badSet_large_le, ZInQ.Density.BadSetOf, ZInQ.Density.latticePts, ZInQ.Density.card_latticePts_le, ZInQ.Density.card_badSet_le_latticePts, ZInQ.Density.card_badSet_le, ZInQ.Density.sum_card_latticePts_le, ZInQ.Density.sum_inv_sq_le_of_gt
---

# The primes bad at a large $\ell$

For every prime $\ell$ and every $N$,
$$\#\bigl(\mathrm{Bad}_\ell\cap[0,N]\bigr)\le\frac{8N}{\ell^2}+\frac{4\sqrt N}{\ell},$$
and the left side is $0$ when $\ell>\sqrt N$. Consequently, for $N\ge1$ and every finite set $F$ of
primes $\ell$ with $\ell^4>N$,
$$\sum_{\ell\in F}\#\bigl(\mathrm{Bad}_\ell\cap[0,N]\bigr)\le20\,N^{3/4}.$$

The Lean statement takes for $c_p$ any function with $p=c_p^2+e^2$ for some $e$, for the primes in
the class; the instance is $c_p=\varphi_p(1)/2$.

**Proof sketch.** By the description, $p=c_p^2+e_p^2$, so $p\mapsto(c_p,e_p)$ embeds
$\mathrm{Bad}_\ell\cap[0,N]$ into the lattice points $(c,e)\in[-\sqrt N,\sqrt N]^2$ with $c\ne0$,
$\ell\mid c$ and $\ell\mid e^2+1$ (from $\ell\mid p+1=c^2+e^2+1$). There are at most
$2\sqrt N/\ell$ nonzero multiples of $\ell$ in the interval (none if $\ell>\sqrt N$), and $e$ lies in
at most two residue classes modulo $\ell$, each meeting the interval in at most $2\sqrt N/\ell+1$
points. Summing $8N/\ell^2+4\sqrt N/\ell$ over the primes $\ell\in F$: the second term vanishes for
$\ell>\sqrt N$, and $\sum_{\ell>N^{1/4}}\ell^{-2}$ and $\sum_{N^{1/4}<\ell\le\sqrt N}\ell^{-1}$ are of
order $N^{-1/4}$ and $N^{1/4}$, giving $20N^{3/4}$.

## Depends on

- [A subset of good slope primes](good-subset.md)

## Proof depends on

- [The description of the good slope primes](description.md)

## Sources

- [The lattice count](../../sources/density-locators.md#the-lattice-count)
