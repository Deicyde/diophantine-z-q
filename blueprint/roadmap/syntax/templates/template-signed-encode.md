---
article_id: af_23632f8c3d5486f9e9e9d40e
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.signedEncodeTemplate, ZInQ.Syntax.signedEncode_facts
---

# The signed-encoding template

The template $\mathtt{value.signed\_encode}$ has $10$ parameters and $140654$ witnesses
($140664$ variables). Parameters: points $N=(X_0,\dots,X_4)$ and $C=(X_5,\dots,X_9)$.
Witnesses in allocation order: points $Q=(X_{10},\dots,X_{14})$, $Q_2=(X_{15},\dots,X_{19})$,
$Q_+=(X_{20},\dots,X_{24})$; $\mathtt{member}$ blocks $[25,32)$ and $[32,39)$; a
$\mathtt{natural}$ block $[39,140643)$; a $\mathtt{raw\_add}$ block $[140643,140649)$; the
rational constants $c_1=X_{140649}$, $c_2=X_{140650}$, $c_3=X_{140651}$ of the generator point
$G=(0,c_1,-145,c_2,c_3)$; and $\mathtt{raw\_add}$ blocks $[140652,140658)$ and
$[140658,140664)$. The formula is
$$\varphi=\bigwedge\Bigl(\langle\mathtt{member}[N]\rangle,\ \langle\mathtt{member}[C]\rangle,\ \langle\mathtt{natural}[Q]\rangle,\
\langle\mathtt{raw\_add}[Q,Q,Q_2]\rangle,\ \bigvee\bigl(\bigwedge(\mathrm{eq}(N,Q),\mathrm{eq}(C,Q_2)),\ \beta\bigr)\Bigr),$$
$$\beta=\bigwedge\bigl(\langle\mathtt{raw\_add}[Q,G,Q_+]\rangle,\ \mathrm{eq}(N,\mathrm{neg}(Q_+)),\ \langle\mathtt{raw\_add}[Q_2,G,C]\rangle\bigr),$$
the two calls in $\beta$ using the blocks $[140652,140658)$ and $[140658,140664)$, and the
polynomial is
$$(8c_1-1641)^2+(4c_2+15465)^2+(32c_3-87483)^2+\kappa(\varphi)^2 .$$
The generator equations stay outside the internal disjunction.

With $Q=\iota(q)$, $q\ge0$, the branches are $C=\iota(2q)$, $N=\iota(q)$ and
$C=\iota(2q+1)$, $N=\iota(-(q+1))$: the template says $N=\iota(\mathrm{dec}(c))$ for
$C=\iota(c)$, $c\ge0$, where $\mathrm{dec}(c)=c/2$ for even $c$ and $-(c+1)/2$ for odd $c$.

This is a definition (template index $13$).

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)
- [Quadratic-field pairs and point-code formulas](../language/field-pair-gadgets.md)
- [The membership template](../template-member.md)
- [The natural-code template](template-natural.md)
- [The raw addition template](../template-raw-add.md)

## Sources

- [Section 2.1](../../../sources/syntax-locators.md#section-21-literal-operations)
- [Section 10.4](../../../sources/syntax-locators.md#section-10-translation)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
