---
article_id: af_71df4dd906825832a7c2fdb0
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.GreenTaoDense.wTrickedSetWeight, ZInQ.GreenTaoDense.wTrickedSetWeight_nonneg, ZInQ.GreenTaoDense.wTrickedSetWeight_le, ZInQ.GreenTaoDense.wTrickedSetWeight_pos_iff
---

# The W-tricked weight of a set of primes

Let $N\ge1$, let $\alpha$ be real and $W,b$ natural numbers, and for $n\in\mathbb Z/N$ let $\bar n$ be
its representative in $[0,N)$. The *W-tricked prime weight* of the Green–Tao proof is
$$\lambda_{\alpha,W,b}(n)=\begin{cases}\alpha\,\dfrac{\varphi(W)}{W}\log(W\bar n+b)&\text{if }
\lfloor N/64\rfloor\le\bar n\le\lfloor N/4\rfloor\text{ and }W\bar n+b\text{ is prime},\\[1ex]
0&\text{otherwise.}\end{cases}$$
For a set $A$ of natural numbers, the *W-tricked weight of $A$* is
$\lambda^A_{\alpha,W,b}(n)=\lambda_{\alpha,W,b}(n)$ if $W\bar n+b\in A$ and $0$ otherwise. If
$\alpha\ge0$, then $0\le\lambda^A_{\alpha,W,b}\le\lambda_{\alpha,W,b}$; if $\alpha>0$ and $W>0$, then
$\lambda^A_{\alpha,W,b}(n)>0$ exactly when $\lfloor N/64\rfloor\le\bar n\le\lfloor N/4\rfloor$ and
$W\bar n+b$ is a prime in $A$.

The bound $\lambda^A\le\lambda$ is what lets the weight of $A$ inherit, unchanged, the majorization
of the prime weight by the Selberg-sieve majorant and its pointwise height bound.

## Depends on

None.

## Sources

- [Where the primes enter](../../sources/green-tao-locators.md#where-the-primes-enter)
- [The Lean statements](../../sources/green-tao-locators.md#the-lean-statements)
