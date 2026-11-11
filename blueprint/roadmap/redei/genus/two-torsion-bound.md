---
article_id: af_4370256ecd82cb5f244f7666
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.card_ker_sq_le
---

# A bound for the 2-torsion of the class group

Let $n>1$ be odd and squarefree, $\mathrm{Cl}$ the class group of the ring of integers of
$\mathbb Q(\sqrt{-n})$ and $t=|T_n|$. Then
$$|\mathrm{Cl}[2]|\le2^{t-1}.$$

**Proof sketch.** $|\ker\psi|\cdot|\mathrm{im}\,\psi|=|\mathbb F_2^{T_n}|=2^t$, and
$\mathrm{im}\,\psi=\mathrm{Cl}[2]$. The kernel contains $e_n$, which is nonzero because $n>1$ has
a prime factor; so $|\ker\psi|\ge2$, and in particular $t\ge1$. Hence
$|\mathrm{Cl}[2]|\le2^t/2=2^{t-1}$.

## Depends on

- [The ramified primes and the ideals $\mathfrak p_p$](../field/ramified-primes.md)
- [The genus class number](../genus-class-number.md)

## Proof depends on

- [The ambiguous class map $\psi$](ambiguous-class-map.md)
- [The ambiguous classes fill $\mathrm{Cl}[2]$](two-torsion.md)
- [The classes of the ramified primes](ramified-classes.md)

## Sources

- [Step 3: ambiguous classes](../../../sources/redei-locators.md#step-3-ambiguous-classes)
