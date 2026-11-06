---
article_id: af_c2a8f50aff5fefa4d14a7983
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.Precision.accepts, ZInQ.Compiler.Precision.acceptsInt, ZInQ.Compiler.Precision.accepts_iff
---

# The precision relation

For $c\in\mathbb N^5$ let $(n,\kappa,a,l,j)\in\mathbb Z^5$ be its signed decoding. The
*precision relation* $\operatorname{accepts}(c)$ holds if and only if all of the following
hold:

1. (early tests) $n\notin\mathcal C=\{0,-15,-20,-24,-30,-60\}$, $\kappa\ne0$, $a\ge1$, $l\ge1$
   and $j=na$;
2. (admissibility) $l$, $a$ and $j$ are admissible indices;
3. (closeness) $|r(a,j)-n|<\epsilon_l$;
4. (precision) $4\epsilon_l<4^{-\mathcal B(n,\kappa)}$, that is
   $4\,\epsilon_l\cdot4^{\mathcal B(n,\kappa)}<1$, with
   $\mathcal B(n,\kappa)=A^{(0)}_{\rm ht}|\kappa F(n)|^{24}$.

Both final tests are strict inequalities between rational numbers (equivalently, between
real numbers). This is the predicate called $\operatorname{accepts\_naturals}$ in equation
(C.4).

This is a definition. Item 2 is implicit in the manuscript, which defines $z$ only on
nonzero multiples of $P_0$; given the generator theorem it follows from item 1, so the
relation is the manuscript's on every input where the latter is meaningful.

## Depends on

- [The signed encoding of integers](signed-encoding.md)
- [The local parameter z on multiples of the generator](z-coordinate.md)
- [The precision height constant](precision-height-constant.md)

## Sources

- [Section 10 decision predicate](../../../../sources/compiler-natural-locators.md#section-10-decision-predicate)
- [Section 10.3 specialization](../../../../sources/compiler-natural-locators.md#section-103-specialization)
