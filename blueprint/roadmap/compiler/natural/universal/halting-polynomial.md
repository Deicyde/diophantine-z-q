---
article_id: af_dc8b790c97298ce333d4c3be
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.Universal.haltingCircuit
---

# The universal halting circuit

The *universal halting circuit* $\mathcal H$ is the compiled circuit
$\mathcal C_{\mathcal U,2}$ of the packed-history construction of the universal interpreter
with $r=204$ registers and $k=2$ inputs $e=X_0$, $n=X_1$: a natural circuit whose explicit
variables are the inputs $X_0,X_1$ followed by the fresh variables of the construction,
whose call nodes are the power calls of the construction with their private blocks of $79$
variables, and whose root is the encoding of the conjunction of the construction. Its node
list begins with the variable nodes of $e$ and $n$; the program literal of the interpreter
does not occur in it (the interpreter is compiled, the interpreted program is an input).
Its numbers of variables, calls and nodes are recorded in the counting statement and the
node-statistics check.

This is a definition.

## Depends on

- [The packed-history construction](../packed/packed-compiler.md)
- [The universal interpreter](universal-interpreter.md)

## Sources

- [Section 10.1 wrapper specialization](../../../../sources/compiler-natural-locators.md#section-101-wrapper-specialization)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
