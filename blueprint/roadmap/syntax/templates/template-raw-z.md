---
article_id: af_635b4bfae544de66fca32b91
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.rawZTemplate, ZInQ.Syntax.rawZTemplate_rel_iff
---

# The local parameter template

The template $\mathtt{raw\_z}$ has $7$ parameters and $1$ witness ($8$ variables): the point
$p=(X_0,\dots,X_4)$, the pair $\zeta=(X_5,X_6)$, and the inverse witness $X_7$ of the
local-parameter gadget. Its formula is $Z(p,\zeta)$ and its polynomial is
$[\![\mathtt{raw\_z}]\!]=\kappa(Z(p,\zeta))^2$. It expresses $\zeta=z(p)=-x(p)/y(p)$, with
$z(O)=0$, on codes of points of $2E(K_0)$.

This is a definition (template index $2$).

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)
- [Quadratic-field pairs and point-code formulas](../language/field-pair-gadgets.md)

## Sources

- [Section 6](../../../sources/syntax-locators.md#section-6-multiplication-template)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
