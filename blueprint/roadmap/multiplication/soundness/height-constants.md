---
article_id: af_015126792f69c15745677c4b
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Mult.heightB0, ZInQ.Mult.heightB0_lt_ten, ZInQ.Mult.one_lt_log_41_sub
---

# Explicit height constants

1. $B_0:=4\log3+\tfrac32\log2+2\log(1+\sqrt2)+\tfrac13\log676<10$.
2. $\log41-\tfrac13\log392>1$.

Numerically $B_0\approx9.369$ and $\log41-\tfrac13\log392\approx1.723$. The numerical
content is isolated in the integer inequalities behind the height constants; this lemma is
the passage from them to the real statements.

**Proof sketch.** Multiply (1) by $6$ and (2) by $3$ and exponentiate: (1) is
$3^{24}\cdot2^9\cdot(1+\sqrt2)^{12}\cdot676^2<e^{60}$ and (2) is $392\,e^3<41^3$. Expand
$(1+\sqrt2)^{12}=(17+12\sqrt2)^3=19601+13860\sqrt2$, which is $<39202$ because
$13860\sqrt2<19601$ follows from $2\cdot13860^2<19601^2$. With $e>2.718$, (1) follows from
$3^{24}\cdot2^9\cdot39202\cdot676^2<(2718/1000)^{60}$, and with $e<2.7183$, (2) follows from
$392\cdot(27183/10^4)^3<41^3$; both are the integer inequalities after clearing denominators.

## Depends on

None.

## Proof depends on

- [The integer inequalities behind the height constants](height-constant-integers.md)

## Sources

- [Finite-box deduction](../../../sources/multiplication-locators.md#finite-box-deduction)
