---
article_id: af_502bc0108d251ff8c4634664
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.catalogue_size
---

# Size of $N_s$ and $\ell$

Assume the catalogue bound. Then
$$1\le N_s=P_sH_{\rm cat}<2^{2^{4613}}\qquad\text{(that is, }\log_2N_s<2^{4613}\text{)},$$
and the pole clearing constant satisfies
$$\ell=12\,P_s^{2916}H_{\rm cat}^{732}<2^{2^{4623}} .$$

**Proof sketch.** All quantities are natural numbers; work with exponents of $2$. With
$X=2^{W^8}$, $H_{\rm cat}\le X^{22W}=2^{22W^9}$ and $P_s<2^{433}$, so
$N_s<2^{433+22W^9}$. From $W<2^{512}$, $W^9<2^{4608}$, so
$433+22W^9<433+22\cdot2^{4608}<32\cdot2^{4608}=2^{4613}$, whence $N_s<2^{2^{4613}}$. For
$\ell$: $12<2^4$, $P_s^{2916}<2^{433\cdot2916}=2^{1262628}$ and
$H_{\rm cat}^{732}\le2^{16104W^9}$, with $16104<2^{14}$, so
$\ell<2^{4+1262628+16104\cdot2^{4608}}<2^{2^{4623}}$. Positivity: $P_s\ge1$ and
$H_{\rm cat}\ge1$.

The manuscript, with the cutoff $2^{W^3}$, states $\log_2N_s<2^{2054}$; the cutoff $2^{W^8}$
of the effective Dirichlet theorem changes the numerals. The bound on $\ell$ is the
companion proof's estimate $\ell<T$, made explicit, and is used for the size of the fixed
constructor.

## Depends on

- [The prescribed fixed constants](../../syntax/constants/fixed-constants.md)
- [The catalogue bound](../../main/catalogue-bound.md)

## Proof depends on

- [Closed numerical comparisons](closed-comparisons.md)
- [Small explicit bounds](small-constant-bounds.md)
- [The catalogue below the progression cutoff](catalogue-bounds.md)

## Sources

- [Proof of Proposition 12.1, catalogue](../../../sources/size-locators.md#proof-of-proposition-121-catalogue)
- [Section 12 opening](../../../sources/size-locators.md#section-12-opening)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
