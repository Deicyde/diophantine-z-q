---
article_id: af_fdd954ec51fe3a6053f6fb98
---

# Syntax heights and the final comparison

The specified polynomial is a compact syntax, not an expanded monomial list: node lists
share nodes, templates call earlier templates, and three constructors insert huge
polynomials without expanding them. Its size is bounded by an induction on this syntax.

## Heights and majorants

Variables have height zero, constants and fixed nodes height one, an operation or
constructor one more than its highest argument, and a call one more than the callee's
height plus its highest argument. Recipes add three levels for a substituted callee in a
model-evaluation recipe, then two for the final sum of squares; composition recipes only
rename variables, so they add two levels for a sum of squares and one for a product.

- [Syntax heights](syntax-height.md)

At height $h\ge1$ a polynomial has degree and logarithmic norm at most $B^{8h}$, provided
$B\ge2^{20}$ exceeds every occurring constant, constructor index and guard cutoff. The six
closure rules (operations, substitution, constructors, renaming, sums of squares and
products) carry this majorant through templates and recipes.

- [Closure rules for the height majorant](majorant-rules.md)
- [Templates satisfy the height majorant](node-majorant.md)
- [Recipes satisfy the height majorant](recipe-majorant.md)

## The specified library

One traversal of the constructed library computes the twenty-three template heights and
checks the constants and constructor indices that occur. The recipe rules then give the
seven recipe heights $228,233,235,251,252,254,256$, using the constraint counts from the
shape of the natural circuit.

- [Template heights](template-heights.md)
- [Recipe heights](recipe-heights.md)

The cutoff $B=T+1$ is admissible: every occurring constant and index is far below $D\le T$.
The root height $256$ gives degree at most $(T+1)^{2048}$ and coefficients at most
$2^{(T+1)^{2048}}$.

- [The cutoff is an admissible bound](admissible-cutoff.md)
- [Degree and coefficient bounds for the specified polynomial](degree-coefficient-bound.md)

## The towers

Since $T<2^{2^{2^{9013}}}$, $(T+1)^{2048}<2^{2^{2^{9014}}}$, and $9014<65536=2\uparrow\uparrow4$
gives the comparisons with $2\uparrow\uparrow7$ and $2\uparrow\uparrow8$, by monotonicity of
exponentiation alone.

- [Comparison with the towers](tower-comparison.md)
