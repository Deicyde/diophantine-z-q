---
article_id: af_5efaee9a7805e7c8d026c681
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.formal_multiple_size
---

# Size of the formal multiple constant

Assume the catalogue bound. Then $1\le M_0\le N_s^{10}$ and
$$c_*=4M_0<2^{2^{4617}} .$$

**Proof sketch.** The existence of a successful formal multiple, applied to $N=N_s\ge1$,
gives $1\le M_0=\mathrm{LFM}(N_s)\le N_s^{10}$. With $N_s<2^{2^{4613}}$,
$c_*\le4N_s^{10}<2^{2+10\cdot2^{4613}}$, and $2+10\cdot2^{4613}<16\cdot2^{4613}=2^{4617}$.

The manuscript, with the cutoff $2^{W^3}$, has $c_*<2^{2^{2059}}$; the cutoff $2^{W^8}$ of
the effective Dirichlet theorem changes the numeral.

## Depends on

- [The prescribed fixed constants](../../syntax/constants/fixed-constants.md)
- [The catalogue bound](../../main/catalogue-bound.md)

## Proof depends on

- [Closed numerical comparisons](closed-comparisons.md)
- [A successful formal multiple](../formal-multiple/formal-multiple-existence.md)
- [Size of $N_s$ and $\ell$](catalogue-size.md)

## Sources

- [Proof of Proposition 12.1, formal multiple](../../../sources/size-locators.md#proof-of-proposition-121-formal-multiple)
- [Proof of Proposition 12.1, cutoff](../../../sources/size-locators.md#proof-of-proposition-121-cutoff)
