---
article_id: af_973a5ed8479f4418c6aba667
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.Natural.powerTemplate, ZInQ.Compiler.Natural.powerTemplate_poly, ZInQ.Compiler.Natural.powerTemplateCircuit_stats
---

# The power template

The *power template* $\mathcal P$ is the template obtained from the natural construction
with $3$ inputs $P=X_0$, $Q=X_1$, $R=X_2$ consisting of the single flat macro
$\mathrm{power}(P,Q,R)$: it has parameter count $3$, variable count $82$ (so $79$
witnesses $X_3,\dots,X_{81}$, all explicit), and polynomial
$$\mathcal P(P,Q,R,w)=\kappa(\mathrm{power}(P,Q,R)),$$
the product of the three branch polynomials (each a sum of squares); it is not squared
again. Its witnesses are, in order: $b,m,a_0,a_1,a_2$; the strict-difference witness of
$0<R$; that of $0<Q$; the $23$ witnesses of $\mathrm{alpha}(a_0,Q+4,R+1)$ (its eight
variables $r,s,t,u,v,w,x,y$ followed by the fifteen gadget witnesses: one each for
$3<b$, $r<s$, $u^2\mid s$, two for each of the four congruences, one each for $2<w$,
$2X<u$, $2X<v$, $2N<u$, in formula order); the witness of $P<m$; the $23$ witnesses of
$\mathrm{alpha}(a_1,b,R)$; the $23$ of $\mathrm{alpha}(a_2,b,R+1)$; the two of the final
congruence. Its node list is the hash-consed node encoding of the construction; its node
statistics ($474$ nodes, constants $0,1,4,2,3,-1$ in order of first occurrence, no calls) are
a finite check of the universal-circuit section.

This is a definition. A *power call* $\mathcal P[g_P,g_Q,g_R;w]$ substitutes the three
parameter polynomials and moves the $79$ witnesses to the block $X_w,\dots,X_{w+78}$, as in
the call semantics of the specification chapter; this is the power interface between the
natural circuit and the power-value recipe.

## Depends on

- [Natural constructions and their macros](natural-constructions.md)
- [Semantics of templates and recipes](../../../syntax/template-semantics.md)

## Sources

- [Section 10.1 saved polynomial](../../../../sources/compiler-natural-locators.md#section-101-saved-polynomial)
- [Section 10.4 power blocks](../../../../sources/compiler-natural-locators.md#section-104-power-blocks)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
