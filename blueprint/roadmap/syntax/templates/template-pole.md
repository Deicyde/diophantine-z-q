---
article_id: af_807a9c14cc628cad3c69ae7a
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.poleTemplate, ZInQ.Syntax.poleTemplate_poly
---

# The pole template

The template $\mathtt{pole}$ has $1$ parameter and $11$ witnesses ($12$ variables): $B=X_0$,
the bits $b_i=X_{1+i}$ ($i=0,\dots,5$), and $e=X_7$, $z=X_8$, $r_1=X_9$, $r_2=X_{10}$,
$w=X_{11}$. With
$$m=(1-2b_0)(1+b_1)(1+2b_2)(1+4b_3)(1+6b_4)(1+12b_5),\quad A=mB,\quad H=A(A-B^2),$$
$$T_1=A(A-e)(A+e),\qquad T_2=A(Az^2-eH)(Az^2+eH),$$
$$S=\sum_{i=0}^5(b_i^2-b_i)^2+(eHzw-1)^2+(r_1^2-T_1)^2+(r_2^2-T_2)^2,$$
its formula is the atom $B\,S\doteq0$ and its polynomial is
$$[\![\mathtt{pole}]\!]=(B\,S)^2=Q_{\rm pole}^2 ,$$
where $Q_{\rm pole}=BS$ is the pole polynomial of the pole completeness statement, with the
witnesses in the same order. Its relation is therefore $\Phi(B)$, as stated in the pole-template
semantics. These are the Route K factors $A+e$ and $Az^2+eH$; the manuscript's template has
$A+3e$ and $Az^2+3eH$.

This is a definition (template index $5$).

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)
- [Pole completeness](../../main/pole-completeness.md)

## Sources

- [Section 6](../../../sources/syntax-locators.md#section-6-multiplication-template)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
