---
article_id: af_327d4215dca6105bac90fe1d
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.PstarNatOf, ZInQ.Syntax.PstarOf, ZInQ.Syntax.Pstar, ZInQ.Syntax.specPstar
---

# The specified polynomial

The specified polynomial is
$$P_*\in\mathbb Z[X_0,X_1,\dots,X_{292890231904}],$$
the polynomial $[\![\mathtt{integers}]\!]$ of the root recipe of the construction, with every
variable of index above $292890231904$ replaced by $0$ (by the witness accounting, no such
variable occurs, so nothing is replaced). Unfolding the root,
$$P_*=\mathtt{value}[X_1,X_2,X_3,X_4,X_5,X_0;6]^2 ,$$
where $\mathtt{value}$ is the composition $\mathtt{member}$ and
$\mathtt{value.exceptions}\times\mathtt{main}$, $\mathtt{main}$ combines $\mathtt{close}$ and
$\mathtt{value.test}$, and $\mathtt{close}$ combines five signed encodings, the precision
recipe and the coordinate window. Variable $X_0$ is the external rational input; the code
$(X_1,\dots,X_5)$ and all further variables are its rational witnesses.

$P_*$ is defined in this blueprint by construction: every template, recipe, fixed
constant and constructor is the term described in this chapter, and the natural
precision circuit is the output of the compiler chapter. The manuscript's saved
specification is compared with this construction by an external script and is not used
in the proof. Its constants are kept symbolic: the
polynomial is never expanded, and the constants $c_*$, $\ell$, $T$, $D$ and the program literal
$c_3$ occur only through their defining expressions.

This is a definition.

## Depends on

- [Semantics of templates and recipes](template-semantics.md)
- [The outer composition recipes](recipes/outer-recipes.md)

## Sources

- [Section 2 opening](../../sources/syntax-locators.md#section-2-opening)
- [Appendix C opening](../../sources/syntax-locators.md#appendix-c-opening)
- [Input B](../../sources/syntax-locators.md#input-b)
- [Saved specification](../../sources/syntax-locators.md#saved-specification)
