---
article_id: af_e6e66a6e31e013f76ddfc3dc
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.Ps, ZInQ.Syntax.W, ZInQ.Syntax.Hcat, ZInQ.Syntax.Hmax, ZInQ.Syntax.Ns, ZInQ.Syntax.M0, ZInQ.Syntax.cstar, ZInQ.Syntax.ell, ZInQ.Syntax.F, ZInQ.Syntax.D, ZInQ.Syntax.G0, ZInQ.Syntax.E0, ZInQ.Syntax.R, ZInQ.Syntax.Q, ZInQ.Syntax.Bcm, ZInQ.Syntax.Ccm, ZInQ.Syntax.Aht, ZInQ.Syntax.T, ZInQ.Syntax.integerConstants, ZInQ.Compiler.Universal.c3
---

# The prescribed fixed constants

The specification binds the following named fixed integer expressions, in this order
(names of the saved specification in parentheses):

| Constant | Definition |
| --- | --- |
| $P_s$ (`P0`) | $\prod_{p\le324,\ p\text{ prime}}p$ |
| $W$ (`W`) | $4P_s$ |
| $H_{\rm cat}$ (`Hproduct`) | $\mathrm{catalogue\_product}(W,22,324)$ |
| $H_{\max}$ (`Hmax`) | $\mathrm{catalogue\_max}(W,22,324)$ |
| $N_s$ (`Ns`) | $P_sH_{\rm cat}$ |
| $M_0$ (`M`) | $\mathrm{least\_formal\_multiple}(N_s)$ |
| $c_*$ (`cstar`) | $4M_0$ |
| $\ell$ (`ell`) | $12\,P_s^{2916}H_{\rm cat}^{732}$ |
| $F$ (`F`) | $324!$ |
| $D$ (`D`) | $F\cdot3^{256F^4}$ |
| $G_0$ (`G0`) | $116064000000$ |
| $E_0$ (`E0`) | $10(DG_0)^2$ |
| $R$ (`R`) | $\max(D,H_{\max},c_*,10^{12})$ |
| $Q$ (`Q`) | $R^{RE_0}$ |
| $B_{\rm cm}$ (`Bcm`) | $D^2\,3^{21000D^2}+1$ |
| $C_{\rm cm}$ (`Ccm`) | $2B_{\rm cm}+4096\bigl((1028+5D)+84000D^2\bigr)$ |
| $A_{\rm ht}$ (`Aheight`) | $2\cdot10^{13}\cdot\max(1,C_{\rm cm},Q^{17})$ |
| $T$ (`T`) | $(48A_{\rm ht})^{13}$ |

The saved specification stores $P_s$ and $W$ as decimal literals; here they are defined by
the displayed products, and their decimal values are a separate finite check. The five
further constants $\mathrm{integer\_constant}_0,\dots,\mathrm{integer\_constant}_4$ are the
nontrivial integer constants of the natural precision polynomial, bound by the
model-evaluation translation (they are $4$, $2$, $3$, the program literal $c_3$, and $1399$).
Here $c_3$ is the code of the wrapper program written for this construction, with
$1399<c_3<2^{2^{24}}$ ([size of the program literal](../../compiler/natural/universal/wrapper-code-size.md));
it is not the saved literal of the manuscript.

$A_{\rm ht}$ is $H_6(S;R)$ of the six-contact estimate at this $R$, and $T$ is the cutoff of
the finite guard. No constant in the table except $G_0$ is evaluated in the proof; the
size chapter bounds them symbolically.

This is a definition.

## Depends on

- [Fixed integer expressions](fixed-integer-expressions.md)

## Sources

- [Appendix C.1](../../../sources/syntax-locators.md#appendix-c1-scalar-nodes)
- [Section 2.2](../../../sources/syntax-locators.md#section-22-catalogue-and-formal-multiple)
- [Saved specification](../../../sources/syntax-locators.md#saved-specification)
