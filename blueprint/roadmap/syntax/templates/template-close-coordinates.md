---
article_id: af_5b9f4ecf1b194e5d21b268ee
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.closeTemplate, ZInQ.Syntax.close_facts
---

# The coordinate-window template

The template $\mathtt{value.close\_coordinates}$ has $16$ parameters and $53$ witnesses
($69$ variables). Parameters: points $A=(X_0,\dots,X_4)$, $L=(X_5,\dots,X_9)$,
$J=(X_{10},\dots,X_{14})$ and $t=X_{15}$. Witnesses in allocation order: pairs
$\zeta_A=(X_{16},X_{17})$, $\zeta_L=(X_{18},X_{19})$, $\zeta_J=(X_{20},X_{21})$; the ratio pair
$q=(X_{22},X_{23})$ and its inverse witness $v=X_{24}$; $a_0=X_{25}$, $a_1=X_{26}$, the distance
$\delta=X_{27}$; the positivity variables $z_1,\dots,z_4=X_{28},\dots,X_{31}$; $\mathtt{member}$
blocks $[32,39)$, $[39,46)$, $[46,53)$; the inverse witnesses $X_{53},X_{54},X_{55}$ of the gadgets
$Z(A,\zeta_A)$, $Z(L,\zeta_L)$, $Z(J,\zeta_J)$; $\mathtt{value.abs}$ blocks $[56,60)$ and
$[60,64)$; the inverse witness $u_\epsilon=X_{64}$; and a $\mathtt{value.abs}$ block $[65,69)$.

With $\epsilon=a_0+a_1$, $r=q_0$ and $\mu=\epsilon-\delta$, the formula is the conjunction of, in
this order: $\langle\mathtt{member}[A]\rangle$, $\langle\mathtt{member}[L]\rangle$,
$\langle\mathtt{member}[J]\rangle$, $\mathrm{fin}(A)$, $\mathrm{fin}(L)$, $Z(A,\zeta_A)$,
$Z(L,\zeta_L)$, $Z(J,\zeta_J)$, $\bigwedge(N(\zeta_A)\,v\doteq1,\ \zeta_A\cdot q\doteq\zeta_J)$,
$\langle\mathtt{value.abs}[(\zeta_L)_0,a_0]\rangle$, $\langle\mathtt{value.abs}[(\zeta_L)_1,a_1]\rangle$,
$\epsilon\,u_\epsilon\doteq1$, $\langle\mathtt{value.abs}[t-r,\delta]\rangle$ and
$\mu\,(z_1^2+z_2^2+z_3^2+z_4^2)\doteq1$. The polynomial is $\kappa$ of it, squared.

It expresses the strict window $|t-\tfrac12\mathrm{Tr}(z(J)/z(A))|<|u_L|+|v_L|$, where
$z(L)=u_L+v_Ls$, for codes $A,L$ of nonzero points.

This is a definition (template index $15$).

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)
- [Quadratic-field pairs and point-code formulas](../language/field-pair-gadgets.md)
- [The membership template](../template-member.md)
- [The absolute-value template](template-abs.md)

## Sources

- [Section 10.4](../../../sources/syntax-locators.md#section-10-translation)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
