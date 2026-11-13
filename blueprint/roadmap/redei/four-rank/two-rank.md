---
article_id: af_48a05b1be6514059f4f6807f
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.card_ker_sq_eq, ZInQ.RouteK.Redei.card_ker_psi
---

# The 2-rank of the class group

Let $n>1$ be odd and squarefree, $\mathrm{Cl}$ the class group of $\mathbb Q(\sqrt{-n})$ and
$t=|T_n|$. Then $|\mathrm{Cl}[2]|=2^{t-1}$, and the kernel of the ambiguous class map
$\psi:\mathbb F_2^{T_n}\to\mathrm{Cl}$ has exactly two elements.

**Proof sketch.** The first claim is part of the principal genus theorem. The image of $\psi$ is
$\mathrm{Cl}[2]$, so $|\ker\psi|\cdot2^{t-1}=|\mathbb F_2^{T_n}|=2^t$. Since $n>1$ has a prime
factor, which lies in $T_n$, $t\ge1$, and $|\ker\psi|=2$.

## Depends on

- [The ambiguous class map $\psi$](../genus/ambiguous-class-map.md)
- [The ramified primes and the ideals $\mathfrak p_p$](../field/ramified-primes.md)

## Proof depends on

- [The principal genus theorem](principal-genus.md)
- [The ambiguous classes fill $\mathrm{Cl}[2]$](../genus/two-torsion.md)
- [There are at least $2^{t-1}$ genera](number-of-genera.md)

## Sources

- [Step 6: the 4-rank](../../../sources/redei-locators.md#step-6-the-4-rank)
- [Step 3: ambiguous classes](../../../sources/redei-locators.md#step-3-ambiguous-classes)
