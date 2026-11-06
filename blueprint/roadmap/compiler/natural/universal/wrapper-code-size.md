---
article_id: af_1c0f94c4bebb496ad2fb94e8
declaration: theorem
origin: bridged
---

# Size of the program literal

Let $c_3=\operatorname{code}(\mathcal W)$ be the code of the wrapper, with $m_{\mathcal W}$
instructions and encoding width $w(\mathcal W)$. Then
$$1399<c_3<2^{20000000}.$$
The bound follows from the two finite facts $m_{\mathcal W}<2^{18}$ and that every register
index and target of $\mathcal W$ is below $2^{18}$: then $w(\mathcal W)\le18$ and
$c_3<2^{18(4m_{\mathcal W}+1)+1}<2^{18874400}<2^{20000000}$; and since $w(\mathcal W)\ge2$ and
$m_{\mathcal W}\ge3$ (a third finite fact), $c_3+1\ge2^{w(4m_{\mathcal W}-7)+1}\ge2^{11}>1400$.

The wrapper of the manuscript has $146{,}780$ instructions (the final halt included),
$23{,}633$ registers and width $18$, so its literal has $10{,}568{,}107$ bits
($3{,}181{,}317$ decimal digits). The precision program of this chapter is written afresh,
so its literal differs; only these bounds are used (by the size bounds, which need every
fixed scalar to have fewer than $20{,}000{,}000$ binary digits, and by the circuit
statistics, which need $c_3\notin\{0,1,-1,2,4,1399\}$). Its value is never computed.

## Depends on

- [The wrapper program](../programs/wrapper-program.md)
- [The universal program numbering](program-numbering.md)

## Proof depends on

- [Codes of primitive programs](program-numbering-encode.md)

## Sources

- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
