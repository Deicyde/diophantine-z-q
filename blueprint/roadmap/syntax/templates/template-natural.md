---
article_id: af_89a3eb758eb92ae19ae4cf29
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.naturalTemplate, ZInQ.Syntax.naturalBuild_formula
---

# The natural-code template

The template $\mathtt{natural}$ has $5$ parameters and $140604$ witnesses ($140609$
variables). Parameter: the point $A=(X_0,\dots,X_4)$. Witnesses in allocation order: points
$\sigma_i=(X_{5+5i},\dots,X_{9+5i})$ and $\Sigma_i=(X_{25+5i},\dots,X_{29+5i})$ for $i=0,\dots,3$; four
$\mathtt{multiply}$ blocks $[45+35134i,\ 35179+35134i)$; the point
$\pi_1=(X_{140581},\dots,X_{140585})$ and a $\mathtt{raw\_add}$ block $[140586,140592)$; the point
$\pi_2=(X_{140592},\dots,X_{140596})$ and a $\mathtt{raw\_add}$ block $[140597,140603)$; and a
$\mathtt{raw\_add}$ block $[140603,140609)$. The formula is
$$\bigwedge\Bigl(\langle\mathtt{multiply}[\sigma_i,\sigma_i,\Sigma_i]\rangle_{i=0,\dots,3},\
\langle\mathtt{raw\_add}[\Sigma_0,\Sigma_1,\pi_1]\rangle,\ \langle\mathtt{raw\_add}[\pi_1,\Sigma_2,\pi_2]\rangle,\
\langle\mathtt{raw\_add}[\pi_2,\Sigma_3,A]\rangle\Bigr),$$
and the polynomial is $\kappa$ of it, squared.

It says that $A$ is the sum of four squares of indices; that, given the multiplication
statement M, its relation holds exactly on $\iota(\mathbb N)$ is the natural-code semantics.

This is a definition (template index $12$).

## Depends on

- [Formulas and their polynomial compilation](../language/formula-compilation.md)
- [The multiplication template](template-multiply.md)
- [The raw addition template](../template-raw-add.md)

## Sources

- [Section 3.1](../../../sources/syntax-locators.md#section-31-membership-and-natural-codes)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
