---
article_id: af_77b1cb4a9058703bba40f431
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.range_sq_eq_ker_chi, ZInQ.RouteK.Redei.range_sq_eq_ker_genusMap_and_card, ZInQ.RouteK.Redei.range_sq_le_ker_genusMap, ZInQ.RouteK.Redei.mem_ker_genusMap, ZInQ.RouteK.Redei.fourRank_sq_eq_one, ZInQ.RouteK.Redei.fourRank_eq_of_mul_eq
---

# The principal genus theorem

Let $n>1$ be odd and squarefree, $\mathrm{Cl}$ the class group of $\mathbb Q(\sqrt{-n})$ and
$t=|T_n|$. Then the subgroup of squares is the intersection of the kernels of the genus
characters,
$$\mathrm{Cl}^2=\bigcap_{q\mid n}\ker\chi_q,$$
which is the kernel of the genus map, and $|\mathrm{Cl}[2]|=2^{t-1}$.

Along the way:

- for every $n\ge1$, a class lies in the kernel of the genus map exactly when $\chi_q$ vanishes
  on it for every prime $q\mid n$, and $\mathrm{Cl}^2$ lies in that kernel, since every element of
  $\mathbb F_2$ has $2x=0$;
- natural numbers with $a\le b$, $c\le d$, $b,c>0$ and $ac=bd$ satisfy $a=b$ and $c=d$.

**Proof sketch.** The genus characters take values in $\mathbb F_2$, so
$\mathrm{Cl}^2\subseteq\ker\chi$. Count:
$$|\mathrm{Cl}^2|\cdot|\mathrm{Cl}[2]|=|\mathrm{Cl}|=|\ker\chi|\cdot|\mathrm{im}\,\chi|.$$
Here $|\mathrm{Cl}^2|\le|\ker\chi|$, and $|\mathrm{Cl}[2]|\le2^{t-1}\le|\mathrm{im}\,\chi|$ by the
bound on the 2-torsion and the number of genera. The arithmetic fact above gives
$|\mathrm{Cl}^2|=|\ker\chi|$, hence $\mathrm{Cl}^2=\ker\chi$, and
$|\mathrm{Cl}[2]|=|\mathrm{im}\,\chi|$, hence $|\mathrm{Cl}[2]|=2^{t-1}$. This is the classical count
of genera, with the principal genus theorem obtained by counting.

## Depends on

- [The genus characters](../genus/genus-characters.md)
- [The genus class number](../genus-class-number.md)
- [The ramified primes and the ideals $\mathfrak p_p$](../field/ramified-primes.md)
- [There are at least $2^{t-1}$ genera](number-of-genera.md)

## Proof depends on

- [A bound for the 2-torsion of the class group](../genus/two-torsion-bound.md)
- [When the subgroup of squares has odd order](odd-square-subgroup.md)

## Sources

- [Step 6: the 4-rank](../../../sources/redei-locators.md#step-6-the-4-rank)
- [The chosen route](../../../sources/redei-locators.md#the-chosen-route)
- [Cox](../../../sources/redei-locators.md#cox)
