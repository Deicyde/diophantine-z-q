---
article_id: af_3300e9c744df987b4cd001c8
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Literature.factNatGenerator, ZInQ.Literature.natGenerator_injective, ZInQ.Literature.exists_natGenerator_eq, ZInQ.Literature.northcott_natCard_residueField, ZInQ.Literature.ePadic, ZInQ.Literature.isUnit_intCast_iff, ZInQ.Literature.irreducible_natGenerator, ZInQ.Literature.maximalIdeal_eq_span, ZInQ.Literature.intCast_mem_maximalIdeal_pow_iff, ZInQ.Literature.natCast_mem_maximalIdeal_iff, ZInQ.Literature.residueEquiv, ZInQ.Literature.natCard_residueField
---

# The places of $\mathbb Q$ and their completions

A *finite place* $v$ of $\mathbb Q$ is a nonzero prime ideal of the ring of integers of
$\mathbb Q$. Write $p_v$ for the positive generator of $v$, $\mathbb Q_v$ for the completion of
$\mathbb Q$ at $v$, $\mathcal O_v$ for its valuation ring, $\mathfrak m_v$ for the maximal ideal of
$\mathcal O_v$ and $\kappa_v=\mathcal O_v/\mathfrak m_v$ for the residue field.

1. $p_v$ is a prime number. Every prime $p$ is $p_v$ for some finite place $v$, and distinct finite
   places have distinct primes.
2. For every natural number $b$, only finitely many finite places $v$ have $\#\kappa_v\le b$.
3. There is a ring isomorphism $\mathcal O_v\cong\mathbb Z_{p_v}$ onto the $p_v$-adic integers.
4. For an integer $n$: $n$ is a unit of $\mathcal O_v$ if and only if $p_v\nmid n$; and for every
   $k\ge0$, $n\in\mathfrak m_v^k$ if and only if $p_v^k\mid n$. For a natural number $n$,
   $n\in\mathfrak m_v$ if and only if $p_v\mid n$.
5. $p_v$ is irreducible in $\mathcal O_v$ and generates $\mathfrak m_v$.
6. There is a ring isomorphism $\kappa_v\cong\mathbb Z/p_v\mathbb Z$, and $\#\kappa_v=p_v$.

**Proof sketch.** (1) The finite places correspond bijectively to the primes by $v\mapsto p_v$.
(3) is the standard identification of the completion of $\mathbb Q$ at $p$ with
$\mathbb Q_p$, restricted to the valuation rings. Transport (4)–(6) along it: in $\mathbb Z_p$ an
integer is a unit exactly when its $p$-adic absolute value is $1$, that is when $p\nmid n$; $p$ is
irreducible, so it is a uniformizer and $\mathfrak m^k=(p^k)$; an integer lies in $p^k\mathbb Z_p$
exactly when $p^k$ divides it; and $\mathbb Z_p/p\mathbb Z_p\cong\mathbb Z/p\mathbb Z$, which has $p$
elements. (2) By (6) $\#\kappa_v=p_v$, and by (1) only finitely many places have $p_v\le b$.

## Depends on

None.

## Sources

- [The L-series of the congruent number curves](../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
