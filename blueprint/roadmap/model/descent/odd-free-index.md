---
article_id: af_82d6f6580fc55182e936b008
declaration: lemma
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.odd_free_index
---

# The free index of $R$ is odd

Let $S\in C(K_0)$ be as in the rank-one theorem and write $R=(1+s,2s)=[m]S+T$ with
$m\in\mathbb Z$ and $T\in C(K_0)[2]$. Then $m$ is odd.

**Proof sketch.** Let $\alpha_C=\alpha_{-\delta^2}$, a homomorphism. The sign vector of a nonzero
element is constant on its squareclass, since squares are totally positive. The class
$\alpha_C(R)=1+s$ has sign vector $(+,-)$. The two-torsion classes are
$\alpha_C(O)=1$, $\alpha_C((0,0))=-\delta^2\equiv-1$, $\alpha_C((\delta,0))=\delta$ and
$\alpha_C((-\delta,0))=-\delta$, all with equal signs because $\delta=3-s$ is totally positive. If
$m$ were even, $\alpha_C(R)=\alpha_C(S)^m\alpha_C(T)\equiv\alpha_C(T)$ would have equal signs. So
$m$ is odd.

## Depends on

- [$E(K_0)$ has rank one](rank-one.md)
- [The certificate for the point $R$](point-r-certificate.md)

## Proof depends on

- [The Kummer map is a homomorphism](kummer-homomorphism.md)
- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../field/special-primes.md)
- [Explicit identities in $K_0$](../field/explicit-identities.md)

## Sources

- [Rank and odd index](../../../sources/model-locators.md#rank-and-odd-index)
