---
article_id: af_53bf154f5363a82dd08c2bfb
declaration: def
origin: cited
statement: formalized
lean: ZInQ.CantorDecoder.pair, ZInQ.CantorDecoder.decode, ZInQ.CantorDecoder.encode5, ZInQ.CantorDecoder.decode5, ZInQ.Compiler.IR.dec5
---

# Cantor pairing and its decoder

The *pairing* of natural numbers is
$$\operatorname{pair}(a,b)=\frac{(a+b)(a+b+1)}2+b,$$
and the five-fold right-nested encoding is
$$\operatorname{enc}_5(c_0,c_1,c_2,c_3,c_4)=\operatorname{pair}(c_0,\operatorname{pair}(c_1,\operatorname{pair}(c_2,\operatorname{pair}(c_3,c_4)))).$$
The *decoder* runs the loop on states $(s,\varrho)$ starting at $(0,x)$: while $s<\varrho$,
replace $(s,\varrho)$ by $(s+1,\varrho-(s+1))$; at exit return $(a,b)=(s-\varrho,\varrho)$. Write
$\operatorname{unpair}(x)$ for the result, and $\operatorname{dec}_5(x)$ for the five numbers
obtained by applying $\operatorname{unpair}$ four times to successive second components
(the last second component is the fifth number).

This is a definition. The loop maintains $\varrho=x-s(s+1)/2$ and terminates because $\varrho$
decreases.

## Depends on

None.

## Sources

- [Section 10.1 wrapper specialization](../../../../sources/compiler-natural-locators.md#section-101-wrapper-specialization)
- [Section 10.3 unpairing and wrapper](../../../../sources/compiler-natural-locators.md#section-103-unpairing-and-wrapper)
