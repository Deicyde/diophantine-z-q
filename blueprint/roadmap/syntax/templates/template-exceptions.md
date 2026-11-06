---
article_id: af_7f12dafb91e4f2dffbdb3f07
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.exceptionsTemplate, ZInQ.Syntax.exceptions_facts
---

# The exceptional-values template

The template $\mathtt{value.exceptions}$ has $6$ parameters and $406$ witnesses ($412$
variables). Parameters: the point $N=(X_0,\dots,X_4)$ and $t=X_5$.

**Chains.** For a point $p$ and an integer $k\ge0$, the double-and-add chain is built as
follows: start with $\mathrm{out}=O$ (the literal code), $\mathrm{base}=p$, $i=0$; while
$k>0$: if $k$ is odd, take a fresh point $\sigma_i$, call
$\langle\mathtt{raw\_add}[\mathrm{out},\mathrm{base},\sigma_i]\rangle$ (a block of $6$) and set
$\mathrm{out}=\sigma_i$; replace $k$ by $\lfloor k/2\rfloor$; if now $k>0$, take a fresh point
$\delta_i$, call $\langle\mathtt{raw\_add}[\mathrm{base},\mathrm{base},\delta_i]\rangle$ and set
$\mathrm{base}=\delta_i$; increase $i$. The chain's formula is the conjunction of its calls (the
empty conjunction for $k=0$) and its value is the final $\mathrm{out}$.

**Variables.** In allocation order: the rational constants $c_1,c_2,c_3=X_6,X_7,X_8$ of the
generator point $G=(0,c_1,-145,c_2,c_3)$; the chains, in the order
$c=0,-15,-20,-24,-30,-60$, for $k=|c|$ on $G$ (for $c=0$) or $\mathrm{neg}(G)$ (for $c<0$),
each raw addition taking its fresh point and then its block; and a $\mathtt{member}$ block
$[405,412)$. The chains have $0,7,6,6,8,9$ raw additions, $36$ in all, occupying
$X_9,\dots,X_{404}$.

**Formula.** With $\beta_c=\bigwedge(\text{chain formula},\ \mathrm{eq}(N,\text{chain value}),\
t\doteq c)$, the formula is
$$\varphi=\bigwedge\Bigl(\langle\mathtt{member}[N]\rangle,\ \bigvee(\beta_0,\beta_{-15},\beta_{-20},\beta_{-24},\beta_{-30},\beta_{-60})\Bigr),$$
and the polynomial is
$$(8c_1-1641)^2+(4c_2+15465)^2+(32c_3-87483)^2+\kappa(\varphi)^2 .$$
The generator equations stay outside the disjunction. The template expresses exactly the
six branches $N=\iota(c)$ and $t=c$ for $c\in\{0,-15,-20,-24,-30,-60\}$.

This is a definition (template index $17$).

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)
- [Quadratic-field pairs and point-code formulas](../language/field-pair-gadgets.md)
- [The membership template](../template-member.md)
- [The raw addition template](../template-raw-add.md)

## Sources

- [Section 2.1](../../../sources/syntax-locators.md#section-21-literal-operations)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Saved specification](../../../sources/syntax-locators.md#saved-specification)
