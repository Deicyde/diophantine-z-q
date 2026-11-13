---
article_id: af_0f26d486b8b236d2c8078e84
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Universal.haltingCircuit_natRel_iff, ZInQ.Compiler.Universal.haltingCircuit_natRel_iff_accepts
---

# Semantics of the universal halting circuit

For all $e,n\in\mathbb N$:
$$Z_{\mathcal H}(e,n)\iff\operatorname{halts}(e,n),$$
that is, $[\![\mathcal H]\!](e,n,v)=0$ for some $v\in\mathbb N^{1305802}$ exactly when the program
numbered $e$ halts on $n$. Replacing $\mathbb N$ by $\mathbb Q$ here is not justified.

**Proof sketch.** The compiled-circuit statement for the valid program $\mathcal U$ gives
$Z_{\mathcal H}(e,n)\iff\mathcal U$ accepts $(e,n)$, and the interpreter's correctness gives
$\iff\operatorname{halts}(e,n)$. Validity comes from the interpreter-shape check and the count
$1{,}305{,}802=1{,}305{,}804-2$ from the counting statement.

## Depends on

- [The universal halting circuit](halting-polynomial.md)
- [The universal program numbering](program-numbering.md)
- [Natural semantics of a natural circuit](../formulas/natural-circuit-semantics.md)

## Proof depends on

- [The compiled circuit of a register machine](../packed/register-machine-polynomial.md)
- [Correctness of the universal interpreter](interpreter-correct.md)
- [Shape of the universal interpreter](interpreter-shape.md)
- [Counts of the universal halting circuit](halting-circuit-counts.md)

## Sources

- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
