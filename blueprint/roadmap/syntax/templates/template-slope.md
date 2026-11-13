---
article_id: af_f499552b4c6f6751e21aea6f
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.slopeTemplate, ZInQ.Syntax.slopeBuild_formula
---

# The slope template

The template $\mathtt{slope}$ has $22$ parameters and $1298$ witnesses ($1320$ variables).
Parameters: $t=X_0$, $\ell=X_1$ and points $C_0,\dots,C_3$ ($C_i=(X_{2+5i},\dots,X_{6+5i})$).
Witnesses in allocation order: $\eta=X_{22}$, $q=X_{23}$, $R_0=X_{24}$; inverse witnesses
$u_1,u_2,u_3,u_4=X_{25},\dots,X_{28}$; for each group $g=0,\dots,5$ with base $\beta=29+213g$:
pairs $D_{g,j}=(X_{\beta+2j},X_{\beta+2j+1})$ ($j=0,\dots,11$), a $\mathtt{test\_group}$ block
$[\beta+24,\beta+186)$, pairs $C'_{g,j}=(X_{\beta+186+2j},X_{\beta+187+2j})$, the pair
$\omega_g=(X_{\beta+210},X_{\beta+211})$ and its inverse witness $v_g=X_{\beta+212}$; then
$B=X_{1307}$, $u_\theta=X_{1308}$ and a $\mathtt{pole}$ block $[1309,1320)$.

Abbreviations: $F(t)=t(t+15)(t+20)(t+24)(t+30)(t+60)$ (left to right, the first factor
written $t+0$); $a=1-R_0q^2$; $R=\ell^2a^2R_0$; $\mathrm{den}_j=R_0(t-1)^2$ for $j<8$ and
$\mathrm{den}_j=R_0^{25}(t-1)^{26}$ for $j\ge8$; $W_g=\prod_{j=0}^{11}\bigl(1+R\,C_{g,j}'^{\,2}\bigr)$ in pair
arithmetic (with $R\,u=(Ru_0,Ru_1)$ and $1=(1,0)$); $\theta=2\sum_{g=0}^5(\omega_g)_0$.

The formula is the conjunction of, in this order:

1. $\eta^2\doteq1$, $(t-1)\,u_1\doteq1$, $F(t)\,u_2\doteq1$, $\ell\,u_3\doteq1$,
   $R_0(t-1)^8\doteq\eta F(t)$, $a\,u_4\doteq1$;
2. for $g=0,\dots,5$: $\langle\mathtt{test\_group}[C_0,\dots,C_3,D_{g,0},\dots,D_{g,11}]\rangle$; the
   pair equations $\mathrm{den}_j\,C'_{g,j}\doteq D_{g,j}$ for $j=0,\dots,11$; and
   $\bigwedge\bigl(N(W_g)\,v_g\doteq1,\ W_g\cdot\omega_g\doteq(1,0)\bigr)$;
3. $\theta\,u_\theta\doteq1$, $B\theta^2\doteq R$, $\langle\mathtt{pole}[B]\rangle$.

The polynomial is $\kappa$ of this conjunction, squared.

This is the normalized six-contact slope certificate: for a slope $t\notin\{0,-15,-20,-24,-30,-60,1\}$
it imposes $R_0=\eta F(t)/(t-1)^8$, $a\ne0$, the normalized tests
$C'_{gj}=D_{gj}/(R_0^{k_j}(t-1)^{k_j+1})$ with $k_j\in\{1,25\}$, $W_g\ne0$, $\theta=\mathrm{Tr}\sum_gW_g^{-1}\ne0$
and $\Phi(R/\theta^2)$.

This is a definition (template index $7$).

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)
- [Quadratic-field pairs and point-code formulas](../language/field-pair-gadgets.md)
- [The test-group template](template-test-group.md)
- [The pole template](template-pole.md)

## Sources

- [Section 6](../../../sources/syntax-locators.md#section-6-multiplication-template)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Saved specification](../../../sources/syntax-locators.md#saved-specification)
