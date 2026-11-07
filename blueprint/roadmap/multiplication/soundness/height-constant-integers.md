---
article_id: af_568e8584779f54fac930a6ab
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Mult.height_constants_int
---

# The integer inequalities behind the height constants

The following three inequalities between natural numbers hold:
$$3^{24}\cdot2^9\cdot39202\cdot676^2\cdot1000^{60}<2718^{60},\qquad
392\cdot27183^3<41^3\cdot10^{12},\qquad 2\cdot13860^2<19601^2 .$$

This is a finite computation. The first compares a number of $205$ decimal digits with one
of $207$ digits (the ratio of the two sides is about $44$); the second compares numbers
below $10^{17}$; the third is $384199200<384199201$.

They are the integer cores of $B_0<10$ and $\log41-\tfrac13\log392>1$: with
$(1+\sqrt2)^{12}=19601+13860\sqrt2$ and $2.718<e<2.7183$, those real inequalities follow from
these three.

**Proof sketch.** Evaluate both sides.

## Depends on

None.

## Sources

- [Finite-box deduction](../../../sources/multiplication-locators.md#finite-box-deduction)
