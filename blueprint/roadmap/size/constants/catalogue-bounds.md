---
article_id: af_38e5d07a33c1516033681ac3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.catalogue_bounds
---

# The catalogue below the progression cutoff

Assume the catalogue bound. Let $W=4P_s$ and $X=2^{W^8}$. For every residue $r$ with
$1\le r<W$ and $\gcd(r,W)=1$ and every $j$ with $1\le j\le22$, the catalogue prime
$p_{r,j}$ (the $j$-th prime $p>324$ with $p\equiv r\pmod W$) satisfies
$$324<p_{r,j}<X .$$
Consequently
$$H_{\max}=\mathrm{catalogue\_max}(W,22,324)<X,\qquad
1\le H_{\rm cat}=\mathrm{catalogue\_product}(W,22,324)\le X^{22W}.$$

**Proof sketch.** Fix such $r$. The hypothesis gives at least $22$ primes $p$ with
$324<p<X$ and $p\bmod W=r$; these are exactly the elements below $X$ of the set
$S_r=\{p\text{ prime}:p>324,\ p\equiv r\pmod W\}$, whose elements in increasing order are
$p_{r,1}<p_{r,2}<\cdots$. So at least $22$ elements of $S_r$ are below $X$, and the
$j$-th element for $j\le22$ is below $X$ (if $\#(S_r\cap[0,X))\ge22>j-1$, then the element
of index $j-1$, counting from $0$, is below $X$). It is above $324$ by definition of $S_r$.
The maximum of finitely many numbers below $X$ is below $X$ (an empty maximum is $0<X$).
The product has $22\,\varphi(W)\le22W$ factors, each in $[1,X)$, so it lies in
$[1,X^{22W}]$.

The manuscript reaches the same conclusion at the smaller cutoff $2^{W^3}$ through the
progression estimate, which gives more than $X/(2W^4)>22$ primes in each unit class and notes
that no prime at most $324$ lies in a unit class. Here the cutoff is $X=2^{W^8}$, the range of
the effective Dirichlet theorem, and the catalogue bound states the needed count directly.

## Depends on

- [The catalogue bound](../../main/catalogue-bound.md)
- [The prime catalogue](../../syntax/constants/prime-catalogue.md)
- [The prescribed fixed constants](../../syntax/constants/fixed-constants.md)

## Sources

- [Proof of Proposition 12.1, catalogue](../../../sources/size-locators.md#proof-of-proposition-121-catalogue)
- [Bennett-Martin-O'Bryant-Rechnitzer](../../../sources/size-locators.md#bennett-martin-obryant-rechnitzer)
