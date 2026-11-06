---
article_id: af_b975b7894233ef9b70af3eb1
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.guardTemplate, ZInQ.Syntax.guardTemplate_rel_iff
---

# The guard template

The template $\mathtt{multiply.guard}$ has $15$ parameters and $1$ witness ($16$ variables):
points $P_0,P_1,P_2$ ($P_i=(X_{5i},\dots,X_{5i+4})$) and the inverse witness $u=X_{15}$. Its
formula is $\mathrm{NZ}(G_T(X_0,\dots,X_{14}))$, the atom $G_T(X_0,\dots,X_{14})\cdot u\doteq1$,
where $G_T$ is the false-triple product at the fixed constant $T$ (the node
$\mathrm{guard}\ T\ (X_0,\dots,X_{14})$). Its polynomial is
$$[\![\mathtt{multiply.guard}]\!]=\bigl(G_T(X_0,\dots,X_{14})\,X_{15}-1\bigr)^2 .$$

This is a definition (template index $10$).

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)
- [The finite false-triple product](../constants/guard-product.md)
- [The prescribed fixed constants](../constants/fixed-constants.md)

## Sources

- [Appendix C.1](../../../sources/syntax-locators.md#appendix-c1-scalar-nodes)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
