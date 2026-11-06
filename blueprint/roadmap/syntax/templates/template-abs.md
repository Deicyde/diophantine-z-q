---
article_id: af_080ff1ab53de42c87d8ec37e
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.absTemplate, ZInQ.Syntax.absTemplate_rel_iff
---

# The absolute-value template

The template $\mathtt{value.abs}$ has $2$ parameters and $4$ witnesses ($6$ variables):
$x=X_0$, $a=X_1$ and $z_1,\dots,z_4=X_2,\dots,X_5$. Its formula is
$\bigwedge(a\doteq z_1^2+z_2^2+z_3^2+z_4^2,\ a^2\doteq x^2)$ and its polynomial is
$$[\![\mathtt{value.abs}]\!]=\bigl((a-z_1^2-z_2^2-z_3^2-z_4^2)^2+(a^2-x^2)^2\bigr)^2 .$$
By the absolute-value statement, $\mathrm{Rel}_{\mathtt{value.abs}}(x,a)\iff a=|x|$.

This is a definition (template index $14$).

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)

## Sources

- [Section 2.1](../../../sources/syntax-locators.md#section-21-positivity-and-absolute-value)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
