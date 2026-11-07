---
article_id: af_1c0f94c4bebb496ad2fb94e8
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Universal.c3, ZInQ.Compiler.Universal.c3_lt, ZInQ.Compiler.Universal.c3_gt
---

# Size of the program literal

Let $c_3=\operatorname{code}(\mathcal W)$ be the code of the wrapper. Then
$$1399<c_3<2^{14400019}<2^{2^{24}}.$$
The value of $c_3$ is never computed; only these bounds are used: by the size chapter, which
needs every literal constant of the specification, $c_3$ included, to be far below the
cutoff (it uses $|c_3|<2^{2^{24}}$), and by the shape of the natural precision circuit, which
needs $c_3\notin\{0,1,-1,2,4,1399\}$.

**Proof sketch.** By the size check, every field of every instruction of $\mathcal W$ (opcode
$0,1,2$, register index, targets) is below $2^{18}$, so the encoding width satisfies
$2\le w(\mathcal W)\le18$. By the bounds for codes of primitive programs,
$c_3<2^{w(4m_{\mathcal W}+1)+1}\le2^{18(4\cdot200000+1)+1}=2^{14400019}$, and
$14400019<16777216=2^{24}$. Since $m_{\mathcal W}\ge3\ge2$ and $w\ge2$,
$c_3+1\ge2^{w(4m_{\mathcal W}-7)+1}\ge2^{2\cdot5+1}=2048$, so $c_3>1399$.

The manuscript's own literal has $10{,}568{,}107$ bits ($3{,}181{,}317$ decimal digits); since
the precision program of this formalization is written afresh, its literal differs, and no
statement depends on its digits.

## Depends on

- [The wrapper program](../programs/wrapper-program.md)
- [The universal program numbering](program-numbering.md)

## Proof depends on

- [Size of the wrapper](wrapper-size-check.md)
- [Codes of primitive programs](program-numbering-encode.md)

## Sources

- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
- [Section 12 literal constants](../../../../sources/compiler-natural-locators.md#section-12-literal-constants)
