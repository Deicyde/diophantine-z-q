---
article_id: af_5d3ffebecf5afff8345ff7cb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Packed.compiled_natRel_iff
---

# The compiled circuit of a register machine

Let $p$ be a primitive program valid for $r$ registers and $1\le k\le r$. For every
$a\in\mathbb N^k$,
$$Z_{\mathcal C_{p,k}}(a)\iff p\text{ accepts }a,$$
where $\mathcal C_{p,k}$ is the compiled circuit of the packed-history construction. In
particular the compiled polynomial has a natural zero with inputs $a$ exactly when $p$
reaches its final halt from the initial file with all registers zero. This holds for every
run length, every size of the register values and every number of inputs.

**Proof sketch.** All macro arguments of the construction are polynomials in previously
allocated variables, so the hierarchical-construction statement applies: $Z_{\mathcal C}(a)$
is equivalent to the existence of natural values of the fresh variables satisfying the
conjunction with every macro replaced by its relation. Soundness and completeness of the
packed-history construction give the two implications.

## Depends on

- [The packed-history construction](packed-compiler.md)
- [Register machines](../programs/register-machine.md)
- [Natural semantics of a natural circuit](../formulas/natural-circuit-semantics.md)

## Proof depends on

- [Circuits of hierarchical constructions](../formulas/hierarchical-calls.md)
- [Semantics of the natural macros](../formulas/macro-semantics.md)
- [Soundness of the packed-history construction](packed-sound.md)
- [Completeness of the packed-history construction](packed-complete.md)

## Sources

- [Section 10.1 transition equations](../../../../sources/compiler-natural-locators.md#section-101-transition-equations)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
