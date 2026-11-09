---
article_id: af_417c255e7157b4106c77aa47
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.precisionRecipe, ZInQ.Syntax.precisionRecipe_variableCount_le
---

# The precision recipe

The recipe $\mathtt{precision}$ is the translation of the five-input natural precision
polynomial in zero mode, with natural constraints on the inputs and with power recipe
$\mathtt{power\_value}$, performed after the translation of the power template (so the
constants $4,2,3$ keep their indices $0,1,2$). It has $25$ parameters (the five input codes
$X_{5i},\dots,X_{5i+4}$, $i=0,\dots,4$, in the input order $(n,\kappa,a,l,j)$), generator indices
$25,26,27$, a natural block for every explicit variable including the inputs, and its root
equality equates the point of the root node with $\mathrm{ref}(-1)$, the code of $O$. Its
nontrivial constants, in order of first occurrence, are $c_3$, $2$, $4$, $1399$; $c_3$ and
$1399$ become $\mathrm{integer\_constant}_3$ and $\mathrm{integer\_constant}_4$.

This is a definition. If the natural circuit has $5$ inputs, listed first among at most
$54056$ explicit variables, at most $125327$ addition, $98382$ multiplication and $15845$ call
nodes, and nontrivial constants among $c_3,2,4,1399$ (the shape given by the natural circuit
statistics), then $\mathtt{precision}$ has at most $292{,}889{,}492{,}836$ witnesses and at most
$292{,}889{,}492{,}861$ variables.

## Depends on

- [Translation of a natural circuit into a model-evaluation recipe](model-evaluation-translation.md)
- [The power-value recipe](recipe-power-value.md)
- [Semantics of the natural precision polynomial](../../compiler/natural/natural-polynomial-semantics.md)

## Sources

- [Section 10.4](../../../sources/syntax-locators.md#section-10-translation)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
