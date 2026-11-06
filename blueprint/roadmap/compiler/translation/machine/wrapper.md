---
article_id: af_64bc68a739cbd9e7360dcc40
declaration: def
origin: cited
---

# The wrapper and the program literal

Let $\Pi=(I_0,\dots,I_{m-1})$ be a primitive register program in final-halt form whose
registers are below $N$, with $N\ge5$. The *wrapper* of $\Pi$ is
$$W(\Pi)=\Pi_{\rm pre}\ \text{followed by}\ \Pi^{+\ell},$$
where $\Pi_{\rm pre}$ is a primitive block of $\ell$ instructions and $\Pi^{+\ell}$ is $\Pi$ with every
target increased by $\ell$. The block $\Pi_{\rm pre}$, started with $x$ in register $0$ and all
other registers zero, runs the unpairing loop four times, each time on the second component
of the previous result, writes $\operatorname{decode}_5(x)$ into registers $0,\dots,4$, uses only
scratch registers $\ge N$ besides registers $0,\dots,4$, clears its scratch registers and then
jumps to state $\ell$, the first state of $\Pi^{+\ell}$.

The *precision machine* is $\Pi_{\rm prec}=\operatorname{lower}(\mathcal R)$, the lowering of the precision
program, and the *program literal* is
$$c_3=\operatorname{code}\bigl(W(\Pi_{\rm prec})\bigr).$$
In the manuscript's construction $c_3$ has $3\,181\,317$ decimal digits. It enters the natural
precision polynomial as a constant and is used only through this definition: no proof
computes its digits.

This is a definition.

## Depends on

- [Primitive register programs](register-programs.md)
- [The universal program numbering](program-numbering.md)
- [Lowering to a primitive program](lowering.md)
- [The precision program](precision-ir.md)
- [Cantor pairing and unpairing](cantor-unpairing.md)

## Sources

- [Section 10.3 unpairing wrapper](../../../../sources/compiler-translation-locators.md#section-103-unpairing-wrapper)
- [Section 10.3 specialization](../../../../sources/compiler-translation-locators.md#section-103-specialization)
- [Section 10.1 Cantor wrapper](../../../../sources/compiler-translation-locators.md#section-101-cantor-wrapper-and-acceptance)
- [Translation artifacts](../../../../sources/compiler-translation-locators.md#translation-artifacts)
