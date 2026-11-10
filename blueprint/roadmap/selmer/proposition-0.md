---
article_id: af_3470d8eb99cb5fb627363cfe
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Selmer.prop0Statement, ZInQ.RouteK.Selmer.Prop0Statement, ZInQ.RouteK.Selmer.prop0, ZInQ.RouteK.Selmer.sel2_subset_range_selPair, ZInQ.RouteK.Selmer.exists_classInt_eq
---

# Proposition 0

Let $d$ be a squarefree natural number with $d\equiv5\pmod8$, and $\mathcal C_d$ the configuration of
its primes. Then:

1. unknowns $\sigma$ solve the Selmer system $\Sigma(\mathcal C_d)$ if and only if
   $(a(\sigma),b(\sigma))\in\mathrm{Sel}_2(C_d)$;
2. every element of $\mathrm{Sel}_2(C_d)$ is $(a(\sigma),b(\sigma))$ for some unknowns $\sigma$.

With the injectivity of $\sigma\mapsto(a(\sigma),b(\sigma))$, the map is a bijection from the solutions
of $\Sigma(\mathcal C_d)$ onto $\mathrm{Sel}_2(C_d)$; in particular $\mathrm{Sel}_2(C_d)$ has as many
elements as $\Sigma(\mathcal C_d)$ has solutions. The second part needs only $d$ odd.

**Proof sketch.** (1) The local conditions are the rows of the system, at $\infty$, at $2$ and at the
primes of $d$; at the remaining odd primes $a(\sigma)$ and $b(\sigma)$ are prime to $p$ and Lemma G2
gives solubility. (2) For $(a,b)\in\mathrm{Sel}_2(C_d)$, Lemma G1 at the odd primes $p\nmid d$ shows
that $p$ divides neither $a$ nor $b$; being squarefree, $a=\pm2^{a_1}\prod_{p\mid d}p^{u_p}$ and
$b=\pm2^{b_1}\prod_{p\mid d}p^{v_p}$ with exponents in $\{0,1\}$, which defines $\sigma$.

## Depends on

- [The 2-Selmer group of a congruent number curve](selmer-group.md)
- [The Selmer system of a configuration](../route-k/selmer-system.md)
- [The configuration of an odd number and Selmer certificates](../route-k/prime-configuration.md)

## Proof depends on

- [The local conditions are the rows of the Selmer system](local-rows.md)
- [Local solubility at odd primes not dividing d](good-primes.md)

## Sources

- [Proposition 0](../../sources/selmer-locators.md#proposition-0)
