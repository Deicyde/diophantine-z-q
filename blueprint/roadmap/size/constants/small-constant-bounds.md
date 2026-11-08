---
article_id: af_b6b83bc5e59e0921bfd92a5c
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.small_constant_bounds
---

# Small explicit bounds

The following closed inequalities between explicit natural numbers hold, where
$P_s=\prod_{p\le324,\ p\text{ prime}}p$ and $W=4P_s$:

1. $P_s<2^{433}$ and $10^5<W<2^{435}<2^{512}$;
2. $2^{2000}<324!<2^{2250}$;
3. $G_0=116064000000<2^{37}$.

This is a finite computation. The manuscript states $10^5<W<2^{512}$ and
$2^{2000}<F_0<2^{2250}$; the sharper $P_s<2^{433}$ is used for $N_s$ and $\ell$. The lower
bound on $W$ is used to apply the effective Dirichlet theorem at $q=W$, which needs
$W\ge2^{16}$.

**Proof sketch.** Direct evaluation: $P_s$ and $W$ have the decimal values of the
primorial literal, with $433$ and $435$ binary digits; $324!$ has $2241$ binary digits
($2^{2240}<324!<2^{2241}$); and $2^{37}=137438953472$.

## Depends on

- [The prescribed fixed constants](../../syntax/constants/fixed-constants.md)

## Proof depends on

- [Decimal values of the primorial constants](../../syntax/constants/primorial-literal.md)

## Sources

- [Proof of Proposition 12.1, catalogue](../../../sources/size-locators.md#proof-of-proposition-121-catalogue)
- [Proof of Proposition 12.1, cutoff](../../../sources/size-locators.md#proof-of-proposition-121-cutoff)
