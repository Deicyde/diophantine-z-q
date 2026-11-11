---
article_id: af_af71ec8b6402e3bfe9544571
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.redeiB_kernel_iff
---

# The two kernel conditions agree

Let $d$ be odd and $B$ a set of primes of $d$. Let $e_{d_B}\in\mathbb F_2^{T_{d_B}}$ be $1$ at the
primes of $d_B$ and $0$ at $2$. Then every vector of $\mathbb F_2^{T_{d_B}}$ killed by the Rédei
matrix of $d_B$ is $0$ or $e_{d_B}$ if and only if the kernel of $(L_B\mid z_B)$ is trivial for
the bits $a,y,z$ of $d$.

**Proof sketch.** A vector on $T_{d_B}$ corresponds to its restriction $e$ to $B$, together with
its value $e_2$ at $2$ when $2\in T_{d_B}$ (and $e_2=0$ otherwise). Then:

- $2\notin T_{d_B}$ exactly when $d_B\equiv3\pmod4$, that is, when $y(B)=1$;
- the two linear systems agree, by the formula for the Rédei matrix of $d_B$ in the bits;
- $e_{d_B}$ corresponds to $e=1$ on $B$ with $e_2=0$, and $0$ to $e=0$ with $e_2=0$.

## Depends on

- [The Rédei matrix](../redei-matrix.md)
- [The kernel of $(L_B\mid z_B)$ through a square matrix](kernel-square-matrix.md)
- [The ramified primes and the ideals $\mathfrak p_p$](../field/ramified-primes.md)
- [The genus sum $T_{5b}$](../../rank-5b/genus-sum/genus-sum.md)

## Proof depends on

- [The Rédei matrix of $\mathbb Q(\sqrt{-d_B})$ in the bits](matrix-in-bits.md)
- [The primes of $d_B$](primes-of-d-b.md)

## Sources

- [Step 8: the bridge](../../../sources/redei-locators.md#step-8-the-bridge)
