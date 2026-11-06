---
article_id: af_926e4807e1a55d304c80b296
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Precision.four_eps_lt_iff_nat, ZInQ.Compiler.Precision.four_eps_lt_iff, ZInQ.Compiler.Precision.four_eps_mul_pow_lt_one_iff
---

# The precision threshold as an integer comparison

Let $U,V$ be positive natural numbers, $\epsilon=U/V$, and $B\in\mathbb N$. Then
$$4\epsilon<4^{-B}\iff4U\cdot4^B<V\iff4^B\le\left\lfloor\frac{V-1}{4U}\right\rfloor .$$

**Proof sketch.** Multiply by the positive number $V4^B$ for the first equivalence. For the
second, for positive $a$ and $D$ and natural $x$, $ax<D\iff ax\le D-1\iff x\le\lfloor(D-1)/a\rfloor$,
applied with $a=4U$, $x=4^B$, $D=V$.

## Depends on

None.

## Sources

- [Section 10 threshold](../../../../sources/compiler-natural-locators.md#section-10-threshold)
