---
article_id: af_ff781ce8896f17a138da50fb
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.scalarTemplate, ZInQ.Syntax.scalarTemplate_rel_iff
---

# The fixed-scalar templates

For a fixed integer expression $e$ with value $n=\mathrm{val}(e)$, the template $S_e$ has
$10$ parameters and $1$ witness ($11$ variables): points $p=(X_0,\dots,X_4)$ and
$r=(X_5,\dots,X_9)$ and the inverse witness $u=X_{10}$. For an index expression $e'$ write
$\psi_{e'}=(\Psi_{\mathrm{val}(e'),0},\Psi_{\mathrm{val}(e'),1})(p_1,p_2,p_3,p_4)$, the pair of
$\mathrm{psi}$ nodes at $x(p),y(p)$. With $g=\psi_e$, $g_+=\psi_{e+1}$, $g_-=\psi_{e+(-1)}$,
$g_2=\psi_{2\cdot e}$ (index expressions $\mathrm{add}(e,1)$, $\mathrm{add}(e,-1)$,
$\mathrm{mul}(2,e)$), the formula is
$$\bigvee\Bigl(\bigwedge(\mathrm{isO}(p),\mathrm{isO}(r)),\ \
\bigwedge\bigl(\mathrm{fin}(p),\ \mathrm{fin}(r),\ N(g)\,u\doteq1,\ g^2\cdot x(r)\doteq x(p)\cdot g^2-g_+\cdot g_-,\
\bigl(2(g^2)^2\bigr)\cdot y(r)\doteq g_2\bigr)\Bigr)$$
in pair arithmetic, and the polynomial of $S_e$ is $\kappa$ of this formula, squared.

The library contains six instances: $\mathtt{multiply.scalar}=S_{c_*}$ (template index $9$)
and $\mathtt{scalar.integer\_constant}_k=S_{\mathrm{integer\_constant}_k}$ for $k=0,\dots,4$
(template indices $18,\dots,22$). The polynomials $\Psi_{n,c}$ for $n=c_*$ are never expanded.

The second branch is the denominator-cleared form of
$x(r)=x-\psi_{n+1}\psi_{n-1}/\psi_n^2$ and $y(r)=\psi_{2n}/(2\psi_n^4)$ with $\psi_n\ne0$.

This is a definition.

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)
- [Quadratic-field pairs and point-code formulas](../language/field-pair-gadgets.md)
- [Normalized division polynomials and their components](../division-polynomials.md)
- [Fixed integer expressions](../constants/fixed-integer-expressions.md)

## Sources

- [Section 2.2](../../../sources/syntax-locators.md#section-22-division-polynomials)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Saved specification](../../../sources/syntax-locators.md#saved-specification)
