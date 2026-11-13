---
article_id: af_cec96c461a3f26b2458d6ee7
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.GreenTaoDense.frequently_window, ZInQ.GreenTaoDense.frequently_window_of, ZInQ.GreenTaoDense.card_filter_range_le_add_Ioc, ZInQ.GreenTaoDense.card_filter_range_le_sum_windows, ZInQ.GreenTaoDense.isLittleO_sqrt_mul_log, ZInQ.GreenTaoDense.eventually_window_error
---

# The window lemma

Let $A$ be a set of natural numbers of positive relative upper density in the primes, with
$c\,\pi(N)\le\#(A\cap[0,N])$ for infinitely many $N$, where $c>0$. Put $c_1=c\log2/24$. Then for
infinitely many $Z$,
$$\#\bigl(A\cap(\lfloor Z/2\rfloor,Z]\bigr)\ge\frac{c_1Z}{\log Z}.$$
In particular some $c_1>0$ has this property.

The set $A$ need not consist of primes. The point is that the density hypothesis, which counts all
of $[0,N]$, yields mass in a window of ratio $2$, which is what the sampling of the W-trick sees.

**Proof sketch.** Let $N$ be large with $c\,\pi(N)\le\#(A\cap[0,N])$, and let $J$ be the largest
integer with $2^J\le\lfloor\sqrt N\rfloor$. Cut $[0,N]$ into the tail $[0,\lfloor N/2^J\rfloor]$ and
the windows $(\lfloor N/2^{j+1}\rfloor,\lfloor N/2^j\rfloor]$ for $j<J$. The tail has at most
$2\sqrt N+1$ elements. Every window has $Z_j=\lfloor N/2^j\rfloor\ge\lfloor\sqrt N\rfloor$, so
$\log Z_j\ge\frac13\log N$ for large $N$, and $Z_j$ tends to infinity with $N$. If every
window had fewer than $c_1Z_j/\log Z_j$ elements of $A$, the windows together would hold fewer than
$\sum_j 3c_1Z_j/\log N\le6c_1N/\log N=\frac c4\log2\cdot N/\log N$ elements. Chebyshev's lower bound
$\pi(N)\log N\ge N\log2-\log(N+1)$ then gives
$c\,\pi(N)>\#(A\cap[0,N])$ once the error terms $(2\sqrt N+2)\log N+c\log(N+1)$ are below
$\frac34c\log2\cdot N$, which holds for large $N$ because $\sqrt x\log x=o(x)$. So for every large
such $N$ some window, with $Z_j\ge\lfloor\sqrt N\rfloor$, is good. Only the lower bound for $\pi$ is used.

## Depends on

- [Szemerédi's theorem in the primes](dense-form.md)

## Sources

- [The proof for a dense set](../../sources/green-tao-locators.md#the-proof-for-a-dense-set)
- [The Lean statements](../../sources/green-tao-locators.md#the-lean-statements)
