---
article_id: af_82d475d89100a55547a93a2b
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.literal_cutoff, ZInQ.Size.formal_multiple_succeeds
---

# The literal cutoff

Assume the catalogue bound. Then the fixed constants of the specification satisfy

1. $R=\max(D,H_{\max},c_*,10^{12})=D$;
2. $T=(48A_{\rm ht})^{13}=(96\cdot10^{13})^{13}\,D^{2210G_0^2D^3}$, where
   $A_{\rm ht}=2\cdot10^{13}\max(1,C_{\rm cm},Q^{17})=2\cdot10^{13}Q^{17}$ and $Q=R^{RE_0}=D^{10G_0^2D^3}$;
3. $T<2^{2^{2^{9013}}}$.

Moreover, the least formal multiple search succeeds: $N_s\ge1$, $1\le M_0\le N_s^{10}$, and the
normalized representation $\xi([M_0]P_0)=(a+bs)/c$ satisfies $N_s^4\mid a$, $N_s^4\mid b$ and
$\gcd(c,N_s)=1$. This part uses the catalogue bound only through $N_s\ge1$ (every catalogue
entry is then a prime above $324$); Dirichlet's theorem on primes in arithmetic progressions
gives $N_s\ge1$ as well, so this part also holds without the hypothesis.

Here $F_0=324!$, $D=F_0\,3^{256F_0^4}$, $G_0=116064000000$, $E_0=10(DG_0)^2$,
$B_{\rm cm}=D^2\,3^{21000D^2}+1$ and $C_{\rm cm}=2B_{\rm cm}+4096(1028+5D+84000D^2)$. This is a statement
about the prescribed integers, independent of the role of $T$ in excluding false
multiplication triples; none of these integers is evaluated.

**Proof sketch.** The catalogue bound puts the catalogue below $X=2^{W^8}$, so
$H_{\max}<X$, $1\le N_s$ and $\log_2N_s<2^{4613}$. The successful formal multiple, applied to
$N=N_s\ge1$, gives $1\le M_0\le N_s^{10}$ and the divisibility conditions,
and hence $c_*<2^{2^{4617}}$, while $2^{2^{8008}}<D<2^{2^{9010}}$; so $R=D$. Then
$C_{\rm cm}<2^{50000D^2}<Q^{17}$ identifies the maximum and gives the closed form of $T$, and the
closed form is below $2^{D^8}<2^{2^{2^{9013}}}$.

## Depends on

- [The prescribed fixed constants](../syntax/constants/fixed-constants.md)
- [The least formal multiple](../syntax/constants/least-formal-multiple.md)
- [The catalogue bound](../main/catalogue-bound.md)

## Proof depends on

- [The parameter $R$ equals $D$](constants/r-equals-d.md)
- [The closed form of $T$](constants/t-identity.md)
- [The cutoff is below a triple tower](constants/t-bound.md)
- [Size of $N_s$ and $\ell$](constants/catalogue-size.md)
- [Size of the formal multiple constant](constants/formal-multiple-size.md)
- [A successful formal multiple](formal-multiple/formal-multiple-existence.md)

## Sources

- [Proposition 12.1](../../sources/size-locators.md#proposition-121)
- [Section 12 opening](../../sources/size-locators.md#section-12-opening)
- [Proof of Proposition 12.1, catalogue](../../sources/size-locators.md#proof-of-proposition-121-catalogue)
- [Proof of Proposition 12.1, formal multiple](../../sources/size-locators.md#proof-of-proposition-121-formal-multiple)
- [Proof of Proposition 12.1, cutoff](../../sources/size-locators.md#proof-of-proposition-121-cutoff)
- [Proposition 12.1 in the manuscript map](../../sources/manuscript.md#proposition-121)
