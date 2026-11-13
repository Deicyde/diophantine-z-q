---
article_id: af_98571fa7c1951b6d39aa53da
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.pointRef, ZInQ.Syntax.generatorConstraints
---

# Point references

In a model-evaluation recipe with generator variable indices $g_0,g_1,g_2$, a point
reference $r\in\mathbb Z$ with $r\ge-3$ stands for five polynomials:
$$\mathrm{ref}(r)=\begin{cases}
(X_r,X_{r+1},X_{r+2},X_{r+3},X_{r+4}),& r\ge0,\\
(1,0,0,0,0),& r=-1,\\
(0,X_{g_0},-145,X_{g_1},X_{g_2}),& r=-2,\\
(0,X_{g_0},-145,-X_{g_1},-X_{g_2}),& r=-3.
\end{cases}$$
The generator constraints of the recipe are the three polynomials
$$8X_{g_0}-1641,\qquad 4X_{g_1}+15465,\qquad 32X_{g_2}-87483 .$$
Every model-evaluation recipe conjoins them.

This is a definition.

## Depends on

None.

## Sources

- [Appendix C opening](../../../sources/syntax-locators.md#appendix-c-opening)
