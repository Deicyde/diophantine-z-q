---
article_id: af_c84839dd9c19313878382efe
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.IR.precisionMachine, ZInQ.Compiler.IR.precRegs, ZInQ.Compiler.IR.precisionMachine_halts_iff, ZInQ.Compiler.IR.precisionMachine_accepts_iff, ZInQ.Compiler.IR.precisionMachine_correct, ZInQ.Compiler.IR.precisionMachine_valid
---

# The precision machine halts exactly on acceptance

Let $M_{\rm prec}=\mathrm{low}(S_{\rm prec})$, a primitive program valid for its register count
$r_{\rm prec}$, with $5$ inputs. For every $c\in\mathbb N^5$:
$$M_{\rm prec}\text{ halts on }c\iff M_{\rm prec}\text{ accepts }c\iff\operatorname{accepts}(c).$$
When $\operatorname{accepts}(c)$ fails, the run of $M_{\rm prec}$ never halts, although the
ideal program is total.

**Proof sketch.** Correctness of the lowering applied to the total program $S_{\rm prec}$,
followed by the correctness of the precision program. When $\operatorname{accepts}(c)$ fails,
the outcome of $S_{\rm prec}$ on $c$ is $\mathbf{reject}$ and the run of $M_{\rm prec}$ reaches the
permanent self-loop of the lowering.

## Depends on

- [The precision program](precision-ir.md)
- [Lowering to primitive programs](lowering.md)
- [The precision relation](../precision/precision-relation.md)

## Proof depends on

- [Correctness of the lowering](lowering-correct.md)
- [Correctness of the precision program](precision-ir-correct.md)

## Sources

- [Section 10.3 lowering](../../../../sources/compiler-natural-locators.md#section-103-lowering)
