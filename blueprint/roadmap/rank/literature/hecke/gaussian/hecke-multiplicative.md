---
article_id: af_0a9a6462a79a9f3288611081
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.HeckeMult, ZInQ.Contrib.HeckeFE.heckeMult
---

# The Hecke coefficients are multiplicative

For a natural number $d$, the Hecke coefficients are *multiplicative* if
$\lambda_d(mn)=\lambda_d(m)\lambda_d(n)$ for all coprime natural numbers $m,n$, where $\lambda_d$ are
the [Hecke coefficients](hecke-coefficients.md).

For every natural number $d$ the Hecke coefficients are multiplicative.

**Proof sketch.** If $m=0$, coprimality forces $n=1$, and $\lambda_d(1)=1$
([Hecke coefficients](hecke-coefficients.md) (1)); likewise if $n=0$. Let $m,n>0$. Expand
$\bigl(\sum_{A_m}\psi_d\bigr)\bigl(\sum_{A_n}\psi_d\bigr)$ as a sum over $A_m\times A_n$ of
$\psi_d(\alpha)\psi_d(\beta)=\psi_d(\alpha\beta)$ ([Hecke character](hecke-character.md) (2)).
Multiplication maps $A_m\times A_n$ into $A_{mn}$
([Gaussian integers as pairs](norm-fibres.md) (3)) with fibres of exactly four elements
([coprime norms](norm-fibres-coprime.md) (2)), so the product equals $4\sum_{A_{mn}}\psi_d$.
Dividing by $16$ gives $\lambda_d(m)\lambda_d(n)=\lambda_d(mn)$.

## Depends on

- [The coefficients of the Hecke L-series $L(\psi_d,s)$](hecke-coefficients.md)

## Proof depends on

- [The Hecke character $\psi_d$](hecke-character.md)
- [Gaussian integers as pairs, norms and units](norm-fibres.md)
- [Factoring a Gaussian integer along coprime norms](norm-fibres-coprime.md)

## Sources

- [Deuring and the Hecke character](../../../../../sources/hecke-locators.md#deuring-and-the-hecke-character)
