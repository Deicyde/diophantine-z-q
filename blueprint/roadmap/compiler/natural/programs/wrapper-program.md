---
article_id: af_2ed2f2b22110fd6e4bca631a
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.IR.unpairProgram, ZInQ.Compiler.IR.wrapperPrefix, ZInQ.Compiler.IR.relocate, ZInQ.Compiler.IR.wrapper, ZInQ.Compiler.IR.wrapper_valid, ZInQ.Compiler.IR.wrapper_size
---

# The wrapper program

Let $M_{\rm prec}$ have $m_{\rm prec}$ instructions and register count $r_{\rm prec}$. The
*wrapper* $\mathcal W$ is the primitive program
$$\mathcal W=\Pi\ \|\ (M_{\rm prec}\text{ with every target increased by }|\Pi|),$$
where the *prefix* $\Pi$ is the open code (the lowering without its termination stage) of
the following program of the ideal register language, with all its registers other than $0,\dots,4$ (working registers, auxiliary registers and
its own jump register) at indices at least $r_{\rm prec}$: starting with the input $x$ in register $0$, compute
$(c_0,y_1)=\operatorname{unpair}(x)$, $(c_1,y_2)=\operatorname{unpair}(y_1)$,
$(c_2,y_3)=\operatorname{unpair}(y_2)$, $(c_3,c_4)=\operatorname{unpair}(y_3)$ by the decoder loop
(subtract $s+1$ from the remainder while $s$ is below it), place $c_i$ in register $i$ for
$i\le4$, clear every register it used at index at least $r_{\rm prec}$, after which the normal exit of $\Pi$ is the first state of the
relocated $M_{\rm prec}$.
Registers of $M_{\rm prec}$ are not renamed; only its targets are relocated by $|\Pi|$, and
its final halt is the final halt of $\mathcal W$.

This is a definition. $\mathcal W$ is valid for $\max(r_{\rm prec},r_\Pi)$ registers and has one
input.

## Depends on

- [Cantor pairing and its decoder](cantor-pairing.md)
- [Lowering to primitive programs](lowering.md)
- [The precision machine halts exactly on acceptance](precision-machine.md)

## Sources

- [Section 10.1 wrapper specialization](../../../../sources/compiler-natural-locators.md#section-101-wrapper-specialization)
- [Section 10.3 unpairing and wrapper](../../../../sources/compiler-natural-locators.md#section-103-unpairing-and-wrapper)
