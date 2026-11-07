---
article_id: af_7f1f830e5947b36868d22522
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Universal.runs_unconsBlock, ZInQ.Compiler.Universal.runs_consBlock, ZInQ.Compiler.Universal.runs_getStmt, ZInQ.Compiler.Universal.runs_setStmt
---

# List blocks of the interpreter

With the conventions of the arithmetic blocks, the interpreter has blocks with the
following effects, each terminating after finitely many steps:

1. *uncons* $x\mapsto(h,t)$: if $x=\operatorname{cons}(h,t)$ then $(h,t)$, and $(0,0)$ for
   $x=\operatorname{nil}$; it copies its input first and halves a positive even value until it is
   odd, each halving strictly decreasing that value;
2. *cons* $(h,t)\mapsto\operatorname{cons}(h,t)$, copying both inputs before the final write, so
   that aliased arguments are safe;
3. *getList* $(L,i)\mapsto\operatorname{get}(L,i)$, following $i$ links (reading past the end
   gives $0$);
4. *setList* $(L,i,v)\mapsto\operatorname{set}(L,i,v)$: save the traversed prefix in reverse,
   replace the selected entry (padding with zeros past the end), then restore the prefix;
   the saved list strictly decreases during restoration.

**Proof sketch.** Compositions of the arithmetic blocks with loops whose measures are the
halved value, the remaining index and the saved reversed prefix; the effect is computed
with the tape-list equations.

## Depends on

- [Tape lists](tape-lists.md)
- [Register machines](../programs/register-machine.md)

## Proof depends on

- [Arithmetic blocks of the interpreter](interpreter-primitives.md)

## Sources

- [Section 10.3 interpreter](../../../../sources/compiler-natural-locators.md#section-103-interpreter)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
