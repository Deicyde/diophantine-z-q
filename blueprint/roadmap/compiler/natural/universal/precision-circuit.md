---
article_id: af_19f9aa24fb035e3a1cf20bc8
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.Universal.specialize, ZInQ.Compiler.Universal.precisionCircuitOf, ZInQ.Compiler.Universal.precisionCircuit
---

# The five-input natural precision circuit

Let $c_3=\operatorname{code}(\mathcal W)$. The *natural precision circuit* $\mathcal N$ is the natural
circuit with $5$ inputs obtained from the universal halting circuit $\mathcal H$ as follows.

1. *Variables.* Inputs $X_0,\dots,X_4$ (the codes $c_0,\dots,c_4$); pairing variables
   $X_5,\dots,X_8$ ($t_0,\dots,t_3$); every variable $X_i$ of $\mathcal H$ with $i\ge2$ becomes
   $X_{i+7}$, and every block start $w$ of $\mathcal H$ becomes $w+7$. The explicit variables
   are listed as $0,\dots,8$ followed by the shifted explicit witnesses of $\mathcal H$, and
   the variable count is that of $\mathcal H$ plus $7$.
2. *Nodes.* The node list of $\mathcal H$, in order, with the variable node of $X_0$ ($e$)
   replaced by the constant node $c_3$, the variable node of $X_1$ ($n$) replaced by the
   variable node of $X_5$, every other variable node and every call block start shifted by
   $7$; followed by the variable nodes of $X_0,\dots,X_4$ and $X_6,X_7,X_8$, the constant
   nodes $1,2,-1$, and, for $i=0,1,2,3$ with $t_4=X_4$ and $c_i=X_i$, the eight nodes of
   $$\pi_i=2t_i+(-1)\cdot\bigl((c_i+t_{i+1})(c_i+t_{i+1}+1)+2t_{i+1}\bigr)$$
   (no hash-consing in this appended part); finally the left-nested sum of squares
   $\rho^2+\pi_0^2+\pi_1^2+\pi_2^2+\pi_3^2$, where $\rho$ is the root of $\mathcal H$, as root.
3. *Power template.* The calls refer to the power template $\mathcal P$.

This is the pinned five-input natural polynomial of input $\mathsf C$, defined by
construction; the saved file is a cross-check of its shape. Its counts ($54{,}056$ explicit
variables, $15{,}845$ private blocks, variable count $1{,}305{,}811$, $293{,}620$ nodes) are
proved in the shape statement.

This is a definition.

## Depends on

- [The universal halting circuit](halting-polynomial.md)
- [The wrapper program](../programs/wrapper-program.md)
- [The universal program numbering](program-numbering.md)
- [The power template](../formulas/power-template.md)
- [Natural semantics of a natural circuit](../formulas/natural-circuit-semantics.md)

## Sources

- [Section 10.1 saved polynomial](../../../../sources/compiler-natural-locators.md#section-101-saved-polynomial)
- [Section 10.1 wrapper specialization](../../../../sources/compiler-natural-locators.md#section-101-wrapper-specialization)
- [Section 10.3 specialization](../../../../sources/compiler-natural-locators.md#section-103-specialization)
- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
