---
article_id: af_45a01c2574b50b0f49bca688
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.D_bounds
---

# Bounds for $D$

With $F_0=324!$ and $D=F_0\,3^{256F_0^4}$,
$$2^{2^{8008}}<D<2^{2^{9010}} .$$

**Proof sketch.** From $2^{2000}<F_0<2^{2250}$. Lower bound: $256F_0^4>2^8\cdot2^{8000}=2^{8008}$
and $3^k>2^k$ for $k\ge1$, so $D\ge3^{256F_0^4}>2^{256F_0^4}>2^{2^{8008}}$. Upper bound:
$3<2^2$ gives $3^{256F_0^4}<2^{512F_0^4}<2^{2^9\cdot2^{9000}}=2^{2^{9009}}$, so
$D<2^{2250}\cdot2^{2^{9009}}=2^{2250+2^{9009}}$, and $2250+2^{9009}<2^{9010}$. Only monotonicity
of $k\mapsto2^k$, $k\mapsto k^4$ and $k\mapsto3^k$ is used; $D$ is not evaluated.

## Depends on

- [The prescribed fixed constants](../../syntax/constants/fixed-constants.md)

## Proof depends on

- [Closed numerical comparisons](closed-comparisons.md)
- [Small explicit bounds](small-constant-bounds.md)

## Sources

- [Proof of Proposition 12.1, cutoff](../../../sources/size-locators.md#proof-of-proposition-121-cutoff)
- [Section 4 constants](../../../sources/size-locators.md#section-4-constants)
