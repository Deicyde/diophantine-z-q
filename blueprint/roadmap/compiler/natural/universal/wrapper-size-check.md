---
article_id: af_bb11037f6ed733007fc51490
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Universal.wrapper_small, ZInQ.Compiler.Universal.wrapper_valid, ZInQ.Compiler.Universal.wrapper_length
---

# Size of the wrapper

The wrapper $\mathcal W$ has $m_{\mathcal W}$ instructions with
$$3\le m_{\mathcal W}\le200{,}000,$$
and every register index and every target occurring in its instructions is below $2^{18}$.

This is a closed decidable statement about the explicit wrapper program, a finite
computation. For comparison, the manuscript's wrapper has $146{,}780$ instructions (the
final halt included), $23{,}633$ registers and encoding width $18$, so it satisfies these
bounds; the wrapper of this formalization is built from a precision program written afresh,
and the bounds are a requirement on it.

## Depends on

- [The wrapper program](../programs/wrapper-program.md)

## Sources

- [Saved precision polynomial](../../../../sources/compiler-natural-locators.md#saved-precision-polynomial)
- [Section 12 literal constants](../../../../sources/compiler-natural-locators.md#section-12-literal-constants)
