---
article_id: af_7dce7659b4e994199f2eaf21
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.IR.wrapper_halts_iff_machine, ZInQ.Compiler.IR.wrapper_halts_iff, ZInQ.Compiler.IR.wrapper_halts_encode
---

# Correctness of the wrapper

For every $x\in\mathbb N$, the wrapper halts on the input $x$ (reaches its final halt from
the file with $x$ in register $0$ and all other registers zero) if and only if
$\operatorname{accepts}(\operatorname{dec}_5(x))$. In particular, for every $c\in\mathbb N^5$,
$$\mathcal W\text{ halts on }\operatorname{enc}_5(c)\iff\operatorname{accepts}(c).$$

**Proof sketch.** The prefix terminates (each decoder loop decreases its remainder) and
reaches the first relocated state with $c_0,\dots,c_4$ in registers $0,\dots,4$, every
auxiliary register cleared, and every other register below $r_{\rm prec}$ still zero (the
prefix touches only registers $0,\dots,4$ and registers at least $r_{\rm prec}$). This is the
initial file of $M_{\rm prec}$ on $(c_0,\dots,c_4)$, extended by zeros. Relocation by $|\Pi|$
is a bijection between the runs of $M_{\rm prec}$ and the runs of the suffix of $\mathcal W$
that preserves the final halt; registers at least $r_{\rm prec}$ are never read by
$M_{\rm prec}$. Hence $\mathcal W$ halts on $x$ iff $M_{\rm prec}$ halts on $\operatorname{dec}_5(x)$,
iff $\operatorname{accepts}(\operatorname{dec}_5(x))$; and $\operatorname{dec}_5(\operatorname{enc}_5(c))=c$.

## Depends on

- [The wrapper program](wrapper-program.md)
- [The precision relation](../precision/precision-relation.md)
- [Cantor pairing and its decoder](cantor-pairing.md)

## Proof depends on

- [Unique Cantor unpairing](cantor-unpairing.md)
- [Correctness of the lowering](lowering-correct.md)
- [The precision machine halts exactly on acceptance](precision-machine.md)

## Sources

- [Section 10.3 unpairing and wrapper](../../../../sources/compiler-natural-locators.md#section-103-unpairing-and-wrapper)
