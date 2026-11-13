---
article_id: af_9ebce2e62ba042030172121d
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Mult.log25_coefficients, ZInQ.Mult.truncLog_eq
---

# The coefficients of the truncated logarithm

For $j=0,1,\dots,6$,
$$16575\cdot\frac{(-1)^j\binom{2j}{j}}{4j+1}=c_j,\qquad
(c_0,\dots,c_6)=(16575,\,-6630,\,11050,\,-25500,\,68250,\,-198900,\,612612),$$
as an identity of rational numbers; moreover $16575=3\cdot5^2\cdot13\cdot17$ and
$d^2=11243-7950s$. Consequently the polynomial
$$L(z)=16575z-6630d^2z^5+11050d^4z^9-25500d^6z^{13}+68250d^8z^{17}-198900d^{10}z^{21}+612612d^{12}z^{25}$$
of the truncated logarithm template is $16575$ times the degree-$25$ truncation
$\sum_{j=0}^{6}(-1)^j\binom{2j}{j}d^{2j}z^{4j+1}/(4j+1)$ of the formal logarithm of $E$.

This is a finite computation: seven rational identities with numbers below $10^6$, and one
factorization.

**Proof sketch.** Evaluate: $\binom{2j}{j}=1,2,6,20,70,252,924$ and $4j+1=1,5,9,13,17,21,25$;
for instance $16575\cdot924/25=663\cdot924=612612$. The truncation statement follows by
comparing coefficients, the template writing $d^{2j}$ as $\delta^j$ with $\delta=d^2$.

## Depends on

- [The truncated logarithm template](../../syntax/templates/template-log25.md)
- [The formal logarithm of $E$ is a binomial series](logarithm-series.md)

## Proof depends on

- [The coefficients of the truncated logarithm](../../syntax/templates/log25-coefficients.md)

## Sources

- [Logarithm series](../../../sources/multiplication-locators.md#logarithm-series)
- [Twelve tests](../../../sources/multiplication-locators.md#twelve-tests)
