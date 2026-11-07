---
article_id: af_69ae2c37eee8a8d5e2ccdf10
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Packed.one_active_state
---

# One active state per time slot

Let $B,q,T=B^q,F_q$ be as in the masked-digit statement, let $1\le m<B$, and let
$S_0,\dots,S_{m-1}$ be masked by $F_q$, with digits $\sigma_i(t)\in\{0,1\}$ ($t\le q$). If
$$S_0+\dots+S_{m-1}=F_q\qquad\text{and}\qquad S_{m-1}=T,$$
then for every $t\le q$ there is exactly one $i<m$ with $\sigma_i(t)=1$, and
$\sigma_{m-1}(t)=1$ if and only if $t=q$. Conversely, if exactly one state digit is $1$ in
each slot $t\le q$ and the last state's digit is $1$ exactly at $t=q$, both equations hold.

**Proof sketch.** In slot $t$ the digits sum to $\sum_i\sigma_i(t)\le m<B$, so the sum of the
$S_i$ is computed without carries and its slot-$t$ digit is $\sum_i\sigma_i(t)$; comparing
with the digit $1$ of $F_q$ gives exactly one active state. $S_{m-1}=B^q$ says the last
state's digits are $0$ except at $t=q$.

## Depends on

- [Digits of masked histories](packed-masks.md)

## Sources

- [Section 10.1 packed histories](../../../../sources/compiler-natural-locators.md#section-101-packed-histories)
