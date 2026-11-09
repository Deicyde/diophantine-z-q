---
article_id: af_4b85c30934543b682e2cec28
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Size.Pstar_degree_coeff, ZInQ.Size.PstarNat_maj
---

# Degree and coefficient bounds for the specified polynomial

Assume the catalogue bound. Then
$$\deg P_*\le(T+1)^{2048},\qquad|[X^\alpha]P_*|\le\|P_*\|_1\le2^{(T+1)^{2048}}\ \text{ for every monomial }X^\alpha .$$

**Proof sketch.** $B=T+1$ is admissible, so the recipe heights give
$\mathrm{Maj}_{T+1}(256,[\![\mathtt{integers}]\!])$: degree at most $(T+1)^{8\cdot256}$ and norm at most
$2^{(T+1)^{2048}}$. By the witness accounting $P_*$ is $[\![\mathtt{integers}]\!]$ with its
variables $X_0,\dots,X_{292890231904}$ kept and nothing replaced, so it has the same degree
and coefficients. Each coefficient is bounded by the $\ell^1$ norm.

## Depends on

- [The specified polynomial](../../syntax/literal-polynomial.md)
- [The prescribed fixed constants](../../syntax/constants/fixed-constants.md)
- [The catalogue bound](../../main/catalogue-bound.md)

## Proof depends on

- [The cutoff is an admissible bound](admissible-cutoff.md)
- [Recipe heights](recipe-heights.md)
- [Witness accounting of the specified polynomial](../../syntax/recipes/witness-accounting.md)
- [Elementary estimates for the coefficient norm](../norms/l1-norm-estimates.md)

## Sources

- [Section 12.1 syntax heights](../../../sources/size-locators.md#section-121-syntax-heights)
- [Companion size proof](../../../sources/size-locators.md#companion-size-proof)
