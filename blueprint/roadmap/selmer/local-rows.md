---
article_id: af_db7889cbaf1e518720304a02
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Selmer.loc_padic_selPair_iff_rows, ZInQ.RouteK.Selmer.classCond_dvd_iff_rows, ZInQ.RouteK.Selmer.loc_real_selPair_iff, ZInQ.RouteK.Selmer.loc_two_selPair_iff_D, ZInQ.RouteK.Selmer.loc_two_selPair_iff, ZInQ.RouteK.Selmer.classCond_two_iff_D, ZInQ.RouteK.Selmer.not_dvd_selPair, ZInQ.RouteK.Selmer.isSol_iff_selPair_mem_of_local, ZInQ.RouteK.Selmer.isSol_iff_selPair_mem_of_G2
---

# The local conditions are the rows of the Selmer system

Let $d$ be an odd squarefree natural number, $\mathcal C_d$ the configuration of its primes, and
$\sigma$ unknowns of $\Sigma(\mathcal C_d)$, with the pair $(a(\sigma),b(\sigma))$.

1. At an odd prime $p\mid d$: $D_{a(\sigma),b(\sigma)}$ is soluble over $\mathbb Q_p$ if and only if
   $\sigma$ satisfies the rows $\mathrm E1_p$ and $\mathrm E2_p$.
2. At the real place ($d\ne0$): it is soluble over $\mathbb R$ if and only if $a_0=b_0$, the row (R).
3. At $2$, for $d\equiv5\pmod8$: it is soluble over $\mathbb Q_2$ if and only if $a_1=0$,
   $b_1=\mu\cdot u$ and $a_0+\lambda\cdot u=b_0+\lambda\cdot v$; given (R) this is the pair of rows (D)
   for the product class $5$.
4. At an odd prime $p\nmid d$, $p$ divides neither $a(\sigma)$ nor $b(\sigma)$.

Consequently, for $d\equiv5\pmod8$ squarefree, $\sigma$ solves $\Sigma(\mathcal C_d)$ if and only if
$(a(\sigma),b(\sigma))\in\mathrm{Sel}_2(C_d)$, provided every pair of integers prime to $p$ is soluble
over $\mathbb Q_p$ at the odd primes $p\nmid d$ (Lemma G2).

**Proof sketch.** Write $a(\sigma)d^i(-1)^j$ and $b(\sigma)2^i(-d)^j$ as $(-1)^s2^t\prod_{q\mid d}q^{e_q}$
and read the square class off the exponents. At $p\mid d$ the valuation forces $i=u_p$, $j=v_p$ and
the residue bit $s\lambda_p+t\mu_p+\sum_{q\ne p}e_q[q/p]$ must vanish; by multiplicativity of the
residue bits the two conditions are $\mathrm E1_p$ and $\mathrm E2_p$. At $2$ the conditions on
$v_2$ and on the characters $\lambda,\mu$ modulo $8$ of the odd parts give $a_1=0$, $b_1=i$,
$\mu\cdot u=i$, $j=a_0+\lambda\cdot u=b_0+\lambda\cdot v$, with $k$ free. The real place is the
sign lemma. Assembling the places gives the equivalence.

## Depends on

- [The 2-Selmer group of a congruent number curve](selmer-group.md)
- [The configuration of an odd number and Selmer certificates](../route-k/prime-configuration.md)

## Proof depends on

- [Squares in the p-adic numbers](padic-squares.md)
- [Local solubility at the real place](real-place.md)
- [Local solubility at odd primes dividing d](bad-odd-primes.md)
- [Local solubility at the place 2](place-two.md)
- [Quadratic reciprocity in residue bits](../route-k/reciprocity-bits.md)

## Sources

- [From classes to the system](../../sources/selmer-locators.md#from-classes-to-the-system)
