---
article_id: af_d4f033ec0307c6e0fd3757f3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Syntax.log25Coeffs_spec
---

# The coefficients of the truncated logarithm

The seven coefficients $(c_0,\dots,c_6)=(16575,-6630,11050,-25500,68250,-198900,612612)$ of the
truncated logarithm template satisfy
$$(4j+1)\,c_j=16575\,(-1)^j\binom{2j}{j}\qquad(j=0,1,\dots,6).$$
Hence $L(z)=16575\sum_{j=0}^{6}\frac{(-1)^j\binom{2j}{j}}{4j+1}d^{2j}z^{4j+1}$, which is $16575$ times the
degree-$25$ truncation of the formal logarithm
$\sum_{j\ge0}\frac{(-1)^j\binom{2j}{j}}{4j+1}d^{2j}z^{4j+1}$ of $E$ in the parameter $z=-x/y$.

This is a closed decidable statement: seven integer identities. The identification of the
series with the formal logarithm of $E$ (from $dx/(2y)=dz/\sqrt{1+4d^2z^4}$) is part of the
multiplication chapter's argument and is not claimed here.

## Depends on

- [The truncated logarithm template](template-log25.md)

## Sources

- [Section 6](../../../sources/syntax-locators.md#section-6-multiplication-template)
