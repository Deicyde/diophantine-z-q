---
article_id: af_df8c5df64eba1db02a7ba912
declaration: def
origin: cited
---

# Formulas and their polynomial compilation

**Formulas.** A formula over $\mathbb Z[X_i:i\in\mathbb N]$ is built from atoms $a\doteq b$
($a,b$ polynomials) and $\langle f\rangle$ ($f$ a polynomial, used for call results) by the
connectives $\bigwedge(\varphi_1,\dots,\varphi_k)$ and $\bigvee(\varphi_1,\dots,\varphi_k)$, $k\ge0$.
A formula holds at $x:\mathbb N\to\mathbb Q$ when its atoms are read as $a(x)=b(x)$ and
$f(x)=0$ and the connectives as conjunction and disjunction (the empty conjunction is
true, the empty disjunction false). Its compilation $\kappa$ is
$$\kappa(a\doteq b)=a-b,\quad \kappa(\langle f\rangle)=f,\quad
\kappa\Bigl(\bigwedge_i\varphi_i\Bigr)=\sum_i\kappa(\varphi_i)^2,\quad
\kappa\Bigl(\bigvee_i\varphi_i\Bigr)=\prod_i\kappa(\varphi_i),$$
with empty sum $0$ and empty product $1$. A conjunction nested inside a conjunction is
squared twice; no flattening takes place.

**Template constructions.** A construction of a template with $p$ parameters keeps a
counter $c$, initially $p$; the parameters are $X_0,\dots,X_{p-1}$. It may:

1. take a fresh variable $X_c$ and increase $c$ by one;
2. call a template or recipe $\tau$ with $m$ witnesses on parameter polynomials $g$: this
   takes the block $X_c,\dots,X_{c+m-1}$, increases $c$ by $m$ and yields the atom
   $\langle\tau[g;c]\rangle$ (a block of length zero takes no variable);
3. request a rational constant $u/q$ with $q\ge2$ (the pair $(u,q)$ normalized only by the
   sign of $q$): the first request in the template takes a fresh variable $X_c$ and records
   the global equation $q\,X_c\doteq u$, and later requests return the same variable; an
   integer constant ($q=1$) is the polynomial $u$ itself.

If the construction ends with formula $\varphi$, recorded global equations $E_1,\dots,E_r$
(in order of creation) and counter $v$, the template is $(p,v)$ with polynomial
$$\kappa\bigl(\textstyle\bigwedge(E_1,\dots,E_r,\varphi)\bigr)=\sum_{i=1}^r\kappa(E_i)^2+\kappa(\varphi)^2 .$$
In particular a template without rational constants has polynomial $\kappa(\varphi)^2$.

**Gadgets.** $\mathrm{NZ}(a)$ takes a fresh $w$ and is the atom $a\cdot w\doteq1$.
$\mathrm{POS}(a)$ takes fresh $z_1,z_2,z_3,z_4$ and is the atom
$a\,(z_1^2+z_2^2+z_3^2+z_4^2)\doteq1$.

**Node encoding.** The node list of a constructed template is produced alongside: an atom
$a\doteq b$ becomes the node $a+(-1)\cdot b$, $\kappa$ of a conjunction a left-nested sum of
squares $x\cdot x$, a disjunction a left-nested product, a call the call node, and
structurally equal nodes are created once. Only the polynomial matters for the semantics;
the node list fixes the syntax heights used in the size chapter and allows comparison with
the saved specification.

This is a definition. Every later template article describes its construction by listing
its variables in allocation order and its formula; the order of the constructor's steps is
the order in which the allocations occur.

## Depends on

- [Semantics of templates and recipes](../template-semantics.md)

## Sources

- [Section 2.1](../../../sources/syntax-locators.md#section-21-literal-operations)
- [Section 10.4](../../../sources/syntax-locators.md#section-10-translation)
- [Saved specification](../../../sources/syntax-locators.md#saved-specification)
