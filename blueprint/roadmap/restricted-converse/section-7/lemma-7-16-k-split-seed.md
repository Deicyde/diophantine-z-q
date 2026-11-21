---
article_id: af_d585ac97013b490771184168
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Wiring.exists_unitSeed_of_ksplit, ZInQ.Manuscript.RC.KSplit.not_appGCongruence
---

# Lemma 7.16: the nonempty $K$-split seed

Let $\ell>0$ be squarefree with $\ell\equiv11\pmod{12}$, let $k$ be odd and squarefree with a prime
$q_0\mid k$, $q_0\nmid2\ell$, and let $K=\mathbb Q(\sqrt k)$. Let $A$ be a symbol on typed graphs and
$S$ a finite set of primes. Assume that if $A$ had no nonempty unit seed, then
$$a_p(E_\ell^{(k)})\equiv p+1\pmod 8$$
at every prime $p\notin S$ with $p\nmid6k\ell$ and $(k/p)=1$ (Elliot's coefficient calculation in
Appendix G, a named input, not proved). Then $A$ has a nonempty unit seed.

In Lean the symbol $A$ is arbitrary: everything that ties it to the positive even source of $E^{(k)}$,
normalized at index one and read on $K$-split primes, is carried by the hypothesis, and "consisting of
$K$-split primes" is not part of the conclusion. The unconditional content is that the congruence fails
(`not_appGCongruence`). In the Lean proof of Theorem 5.3 the lemma enters in an equivalent form, as the
$K$-split seed clause of the field `PostLeaves.address` of [the remaining
hypotheses](../remaining-hypotheses.md).

**Proof sketch.** The fresh prime $q_0$ of $K$ allows a prime $p\notin S$, $p\nmid6k\ell$, with
$p\equiv1\pmod4$, $(\ell/p)=-1$ and $(k/p)=1$. Since $k$ is a square modulo $p$, the reductions of
$E^{(k)}$ and $E_\ell$ are isomorphic over $\mathbb F_p$. None of the three points of order two is
divisible by two, since the required square differences include $-\ell$, $\ell$ and $-4\ell$, all
nonsquares modulo $p$. So the two-primary part of $E_\ell(\mathbb F_p)$ has order four, that is
$v_2(p+1-a_p)=2$, and the congruence fails at $p$.

## Depends on

- [Section 7: unit seeds](README.md)
- [The remaining hypotheses](../remaining-hypotheses.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
