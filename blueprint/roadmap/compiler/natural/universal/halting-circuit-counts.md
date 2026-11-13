---
article_id: af_2a7f593d2afbac60c9bf7394
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Universal.haltingCircuit_counts, ZInQ.Compiler.Universal.haltingCircuit_witnessCount, ZInQ.Compiler.Universal.haltingCircuit_macroCounts
---

# Counts of the universal halting circuit

The universal halting circuit $\mathcal H$ has $54{,}049$ explicit variables (the two inputs
$X_0,X_1$ and $54{,}047$ witnesses), $15{,}845$ calls of the power template with private
blocks of $79$ variables, and variable count
$$54{,}049+79\cdot15{,}845=1{,}305{,}804,$$
so a natural zero with inputs $(e,n)$ has $1{,}305{,}802$ witness coordinates. Its
construction contains $1{,}603$ mask macros, $1{,}226$ bitAnd macros, $3{,}678$ orthogonal
macros, $5{,}281$ binomial macros and $10{,}770$ strict-inequality gadgets. Moreover
$\mathcal H$ is well scoped.

**Proof sketch.** The counting statement of the packed construction with $k=2$, $r=204$,
$m=1{,}399$, $s=1{,}022$ (the shape check): explicit variables
$2k+9+41r+10m+31s=4+9+8364+13990+31682=54{,}049$; calls
$2+3(m+4r+3s)=2+3\cdot5281=15{,}845$; masks $m+r=1603$; bitAnd $r+s=1226$; orthogonal
$3(r+s)=3678$; binomial $m+4r+3s=5281$; strict inequalities $2+k+r+2\cdot5281=10{,}770$.
Well-scopedness is item 1 of the statement on hierarchical constructions, all macro
arguments of the packed construction being polynomials in earlier variables.

## Depends on

- [The universal halting circuit](halting-polynomial.md)
- [Natural semantics of a natural circuit](../formulas/natural-circuit-semantics.md)

## Proof depends on

- [Shape of the universal interpreter](interpreter-shape.md)
- [Variable and gadget counts of the packed construction](../packed/packed-counts.md)
- [Circuits of hierarchical constructions](../formulas/hierarchical-calls.md)

## Sources

- [Section 10.4 power blocks](../../../../sources/compiler-natural-locators.md#section-104-power-blocks)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
