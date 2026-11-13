---
article_id: af_39722d80ee6d4f42379f793e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.binomial_digit_iff_choose
---

# Binomial coefficients as base-B digits

For natural numbers $C,N,K$ the following are equivalent:

1. there are natural numbers $\beta,\tau,\pi,q,r$ with
   $$\beta=2^{N+1},\quad\tau=(\beta+1)^N,\quad\pi=\beta^K,\quad C<\beta,\quad r<\pi,\quad
   \tau=\pi(\beta q+C)+r;$$
2. $C=\binom NK$ (with $\binom NK=0$ for $K>N$).

In particular, with $\beta=2^{N+1}$, the $K$-th base-$\beta$ digit of $(1+\beta)^N$ is
$\binom NK$, including the cases $N=0$, $K=0$ and $K>N$. In the compiler the three powers are
power macros and the witnesses are introduced in the order $\beta,\tau,\pi,q,r$
(`binomial_base`, `binomial_total`, `binomial_place`, `binomial_quotient`,
`binomial_remainder`).

**Proof sketch.** Each $\binom Nj\le2^N<\beta$, so the binomial theorem
$(1+\beta)^N=\sum_{j\le N}\binom Nj\beta^j$ is the base-$\beta$ expansion of $\tau$, with digit
$\binom NK$ at place $K$ (zero for $K>N$). For positive $\beta$ and $\pi$, the existence of
$q,r$ with $C<\beta$, $r<\pi$ and $\tau=\pi(\beta q+C)+r$ is equivalent to
$C=\lfloor\tau/\pi\rfloor\bmod\beta$ (uniqueness of division with remainder, twice). Hence
$C$ is the digit at place $K$.

## Depends on

None.

## Sources

- [Section 10.2 binomial and bits](../../../../sources/compiler-natural-locators.md#section-102-binomial-and-bits)
- [Compiler specification](../../../../sources/compiler-natural-locators.md#compiler-specification)
