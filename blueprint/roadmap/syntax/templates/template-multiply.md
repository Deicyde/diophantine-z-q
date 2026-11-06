---
article_id: af_2113b9179f1833ad7874e383
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.multiplyTemplate, ZInQ.Syntax.multiplyBuild_formula
---

# The multiplication template

The template $\mathtt{multiply}$ has $15$ parameters and $35134$ witnesses ($35149$
variables). Parameters: points $P_0,P_1,P_2$ ($P_i=(X_{5i},\dots,X_{5i+4})$). Witnesses in
allocation order: the rational constants $c_1=X_{15}$ ($1641/8$), $c_2=X_{16}$ ($-15465/4$),
$c_3=X_{17}$ ($87483/32$), giving the generator point $G=(0,c_1,-145,c_2,c_3)$; for
$i=0,\dots,3$ a shift point $S_i=(X_{18+6i},\dots,X_{22+6i})$ followed by an
$S_{c_*}$ block $\{X_{23+6i}\}$; a $\mathtt{height\_certificate}$ block $[42,35148)$; and a
$\mathtt{multiply.guard}$ block $\{X_{35148}\}$.

With $(\Pi_0,\Pi_1,\Pi_2,\Pi_3)=(G,P_0,P_1,P_2)$ and $\ell$ the node $\mathrm{fixed}\ \ell$, the
formula is the conjunction
$$\varphi_{\rm mul}=\bigwedge\Bigl(\langle S_{c_*}[\Pi_0,S_0]\rangle,\dots,\langle S_{c_*}[\Pi_3,S_3]\rangle,\
\langle\mathtt{height\_certificate}[P_0,P_1,P_2,\ell,S_0,S_1,S_2,S_3]\rangle,\
\langle\mathtt{multiply.guard}[P_0,P_1,P_2]\rangle\Bigr),$$
and the polynomial, including the global generator equations, is
$$[\![\mathtt{multiply}]\!]=(8X_{15}-1641)^2+(4X_{16}+15465)^2+(32X_{17}-87483)^2+\kappa(\varphi_{\rm mul})^2 .$$

So the four scalar shifts are $c_*G$, $c_*P_0$, $c_*P_1$, $c_*P_2$, the membership of the three
roots is imposed inside the height certificate, and the guard excludes the false triples
in the box. That $\mathrm{Rel}_{\mathtt{multiply}}$ holds exactly on code triples with indices
$a,b,ab$ is the multiplication statement M.

This is a definition (template index $11$).

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)
- [Quadratic-field pairs and point-code formulas](../language/field-pair-gadgets.md)
- [The fixed-scalar templates](template-fixed-scalar.md)
- [The height certificate template](template-height-certificate.md)
- [The guard template](template-guard.md)
- [The prescribed fixed constants](../constants/fixed-constants.md)

## Sources

- [Section 6](../../../sources/syntax-locators.md#section-6-multiplication-template)
- [Section 2.1](../../../sources/syntax-locators.md#section-21-literal-operations)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
