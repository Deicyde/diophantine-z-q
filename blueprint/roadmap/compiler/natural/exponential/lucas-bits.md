---
article_id: af_2c8d43338ba58957a167ee14
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.lucas_choose_odd_iff_masked, ZInQ.lucas_choose_add_odd_iff_disjoint
---

# Lucas's criterion for bit inclusion and disjointness

For natural numbers $a,b$ write $a\mathbin{\mathrm{AND}}b$ for the bitwise conjunction of their
binary expansions, and say $a$ is *masked by* $b$ when $a\mathbin{\mathrm{AND}}b=a$ (every set bit
of $a$ is set in $b$). Then:

1. $\binom ba$ is odd if and only if $a$ is masked by $b$;
2. $\binom{a+b}a$ is odd if and only if $a\mathbin{\mathrm{AND}}b=0$.

**Proof sketch.** (1) Lucas's theorem at the prime $2$:
$\binom ba\equiv\binom{b\bmod2}{a\bmod2}\binom{\lfloor b/2\rfloor}{\lfloor a/2\rfloor}\pmod2$,
and $\binom{\beta}{\alpha}$ for bits $\alpha,\beta$ is $0$ exactly when $\alpha=1,\beta=0$; induct on
$b$. Equivalently, $(1+t)^b=\prod_{i:\,\mathrm{bit}_i(b)=1}(1+t^{2^i})$ over $\mathbb F_2$.
(2) By (1) it suffices that $a$ is masked by $a+b$ iff $a\mathbin{\mathrm{AND}}b=0$. If the bits
are disjoint the addition has no carries and $a+b=a\mathbin{\mathrm{OR}}b$. Otherwise, at the least
position where both $a$ and $b$ have a set bit there is no incoming carry (below it at most
one summand has each bit set, so no carry is generated), so that bit of $a+b$ is $0$ while
the bit of $a$ is $1$.

## Depends on

None.

## Sources

- [Section 10.2 binomial and bits](../../../../sources/compiler-natural-locators.md#section-102-binomial-and-bits)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
