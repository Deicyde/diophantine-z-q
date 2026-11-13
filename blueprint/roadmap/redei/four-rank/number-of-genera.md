---
article_id: af_fa1bec2fd5f5cf3f1c58f854
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.pow_le_card_range_genusMap, ZInQ.RouteK.Redei.genusMap, ZInQ.RouteK.Redei.genusMap_apply, ZInQ.RouteK.Redei.fourRankSum, ZInQ.RouteK.Redei.fourRankSum_apply, ZInQ.RouteK.Redei.card_ker_fourRankSum, ZInQ.RouteK.Redei.fourRank_primeFactors_nonempty, ZInQ.RouteK.Redei.fourRank_card_ramSet
---

# There are at least $2^{t-1}$ genera

For $n\ge1$ the *genus map* of $\mathbb Q(\sqrt{-n})$ is the homomorphism
$$\chi:\mathrm{Cl}\to\mathbb F_2^{\{q\mid n\}},\qquad c\mapsto(\chi_q(c))_q,$$
indexed by the primes $q\mid n$. Let $n>1$ be odd and squarefree and $t=|T_n|$. Then the image of
the genus map has at least $2^{t-1}$ elements.

Along the way:

- every $n>1$ has a prime factor;
- for odd $n$ with $r$ prime factors, $t=r$ if $n\equiv3\pmod4$ and $t=r+1$ otherwise;
- for a nonempty finite set $I$, the hyperplane $\{e\in\mathbb F_2^I:\sum_ie_i=0\}$, the kernel of
  the sum map $\mathbb F_2^I\to\mathbb F_2$, has $2^{|I|-1}$ elements.

**Proof sketch.** Let $r\ge1$ be the number of primes of $n$.

- If $n\equiv3\pmod4$, then $t=r$. The genus characters take every value with
  $\sum_q\varepsilon_q=0$, so the image of $\chi$ contains the sum-zero hyperplane, which has
  $2^{r-1}$ elements.
- Otherwise $t=r+1$, since $2$ is not a prime of $n$. The genus characters take every value, so
  the image of $\chi$ is all of $\mathbb F_2^r$, which has $2^r=2^{t-1}$ elements.

## Depends on

- [The genus characters](../genus/genus-characters.md)
- [The ramified primes and the ideals $\mathfrak p_p$](../field/ramified-primes.md)

## Proof depends on

- [The genus characters take all allowed values](../genus/surjectivity.md)

## Sources

- [Step 6: the 4-rank](../../../sources/redei-locators.md#step-6-the-4-rank)
- [The chosen route](../../../sources/redei-locators.md#the-chosen-route)
