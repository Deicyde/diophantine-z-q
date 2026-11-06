---
article_id: af_5fa814dc228537e8ad7deccb
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.log25Template, ZInQ.Syntax.log25Template_rel_iff
---

# The truncated logarithm template

The template $\mathtt{log25}$ has $4$ parameters and no witnesses: the pairs
$\zeta=(X_0,X_1)$ and $\lambda=(X_2,X_3)$. With $\delta=(11243,-7950)$ (that is $d^2$) and
$$L(\zeta)=\sum_{j=0}^{6}c_j\,\bigl(\delta^j\cdot\zeta^{4j+1}\bigr),\qquad
(c_0,\dots,c_6)=(16575,\,-6630,\,11050,\,-25500,\,68250,\,-198900,\,612612),$$
computed in pair arithmetic ($\delta^j$ by successive multiplication, $\zeta^{4j+1}$ by repeated
squaring), its formula is the pair equation $L(\zeta)\doteq\lambda$ and its polynomial is
$$[\![\mathtt{log25}]\!]=\bigl((L_0(\zeta)-\lambda_0)^2+(L_1(\zeta)-\lambda_1)^2\bigr)^2 .$$

$L(z)=16575z-6630d^2z^5+11050d^4z^9-25500d^6z^{13}+68250d^8z^{17}-198900d^{10}z^{21}+612612d^{12}z^{25}$
is $16575$ times the degree-$25$ truncation of the formal logarithm
$\sum_{j\ge0}(-1)^j\binom{2j}{j}d^{2j}z^{4j+1}/(4j+1)$ of $E$; that the coefficients are
$16575\cdot(-1)^j\binom{2j}{j}/(4j+1)$ for $j=0,\dots,6$ is a separate finite check.

This is a definition (template index $4$).

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)
- [Quadratic-field pairs and point-code formulas](../language/field-pair-gadgets.md)

## Sources

- [Section 6](../../../sources/syntax-locators.md#section-6-multiplication-template)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
