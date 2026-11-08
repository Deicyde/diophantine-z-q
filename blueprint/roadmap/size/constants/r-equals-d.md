---
article_id: af_b4a0970674dfe0f62cf9b752
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.r_equals_d, ZInQ.Size.R_eq_D
---

# The parameter $R$ equals $D$

Assume the catalogue bound. Then $H_{\max}<D$, $c_*<D$ and $10^{12}<D$; consequently
$$R=\max(D,H_{\max},c_*,10^{12})=D .$$

**Proof sketch.** $H_{\max}<2^{W^8}$ and $W^8<2^{8\cdot512}=2^{4096}$, so
$H_{\max}<2^{2^{4096}}<2^{2^{8008}}<D$. Next $c_*<2^{2^{4617}}<2^{2^{8008}}<D$, and
$10^{12}<2^{40}<D$. A maximum whose first entry dominates the others equals that entry.

## Depends on

- [The prescribed fixed constants](../../syntax/constants/fixed-constants.md)
- [The catalogue bound](../../main/catalogue-bound.md)

## Proof depends on

- [Closed numerical comparisons](closed-comparisons.md)
- [Small explicit bounds](small-constant-bounds.md)
- [The catalogue below the progression cutoff](catalogue-bounds.md)
- [Size of the formal multiple constant](formal-multiple-size.md)
- [Bounds for $D$](d-bounds.md)

## Sources

- [Proof of Proposition 12.1, cutoff](../../../sources/size-locators.md#proof-of-proposition-121-cutoff)
- [Proposition 12.1](../../../sources/size-locators.md#proposition-121)
