---
article_id: af_015126792f69c15745677c4b
declaration: lemma
origin: cited
---

# Explicit height constants

1. $B_0:=4\log3+\tfrac32\log2+2\log(1+\sqrt2)+\tfrac13\log676<10$.
2. $\log41-\tfrac13\log392>1$.

This is a finite computation. After exponentiation, (1) is
$3^{24}\cdot2^9\cdot(1+\sqrt2)^{12}\cdot676^2<e^{60}$ and (2) is $392\,e^3<41^3$. With
$(1+\sqrt2)^{12}=19601+13860\sqrt2<39202$ (because $2\cdot13860^2=384199200<384199201=19601^2$)
and $2.718<e<2.7183$, they follow from the integer inequalities
$$3^{24}\cdot2^9\cdot39202\cdot676^2\cdot1000^{60}<2718^{60},\qquad
392\cdot27183^3<41^3\cdot10^{12} .$$
The first compares numbers of about $206$ decimal digits; numerically $B_0\approx9.369$ and
$\log41-\tfrac13\log392\approx1.723$.

**Proof sketch.** Multiply (1) by $6$ and (2) by $3$ and exponentiate; expand
$(1+\sqrt2)^{12}=(17+12\sqrt2)^3$; bound $e$ by its decimal enclosures; check the two integer
inequalities.

## Depends on

None.

## Sources

- [Finite-box deduction](../../../sources/multiplication-locators.md#finite-box-deduction)
