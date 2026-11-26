---
article_id: af_e30be41e56a6c26ccfce30c1
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Limits.ex_limits_outer_evaluation_5_2
---

# (5.2): the evaluation identities

There are no inputs beyond the data: a complex $C^0\to C^1\to C^2$ over a commutative ring, and a
cochain map from it to the inhomogeneous cochains, in degrees zero to two, of a representation $\rho$
of a group $G$.

For $g,h\in G$ write $e^0$, $e^1_g$ and $e^2_{g,h}$ for the evaluations of the cochain map in degree
zero, at $g$ and at $(g,h)$. Then
$$e^1_gd=(\rho(g)-1)e^0,\qquad e^2_{g,h}d=\rho(g)e^1_h-e^1_{gh}+e^1_g.\tag{5.2}$$

The manuscript evaluates the retained global models and the primitive and derivative Selmer models at
sequences of Galois elements, in the product $\prod_iG_K$ with one simultaneous complex conjugation;
the Lean theorem is the identity at one stage, for any group. That a cycle then gives a crossed
homomorphism of the product group in the inner limit is `ex_limits_outer_evaluation_inner_crossedHom`.

The reduction of Theorem 5.3 does not use this theorem.

**Proof sketch.** The two identities are the commuting squares of the cochain map in degrees zero and
one, read at $g$ and at $(g,h)$; Mathlib's inhomogeneous differentials carry the manuscript's signs.

## Depends on

None.

## Sources

- [Section 9](../../../sources/manuscript.md#section-9)
