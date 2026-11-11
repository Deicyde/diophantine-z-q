---
article_id: af_b8a61101c47bb3496be32ee4
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.delta_add, ZInQ.RouteK.Rank.deltaHom, ZInQ.RouteK.Rank.deltaHom_apply, ZInQ.RouteK.Rank.delta_two_nsmul
---

# The complete 2-descent map is a homomorphism

Let $K$ be a field with $2\ne0$ and $d\in K^\times$. Then $\delta_d(P+Q)=\delta_d(P)\,\delta_d(Q)$
for all $P,Q\in C_d(K)$, so $\delta_d$ is a group homomorphism $C_d(K)\to(K^\times/K^{\times2})^2$.
Moreover $\delta_d(2P)=1$ for every $P\in C_d(K)$, so $2C_d(K)$ lies in its kernel.

**Proof sketch.** Each coordinate of $\delta_d$ is a Kummer map at a root ($0$, respectively $d$)
of $x^3-d^2x$ on $E_{-d^2}$, with $-d^2\ne0$, so each coordinate is a homomorphism, and so is the
pair. Then $\delta_d(2P)=\delta_d(P)^2=1$, since every square class has order dividing $2$.

## Depends on

- [The complete 2-descent map of a congruent number curve](descent-map.md)

## Proof depends on

- [The Kummer map at a root is a homomorphism](kummer-map-at-root-homomorphism.md)

## Sources

- [The complete 2-descent map](../../../sources/rank-locators.md#the-complete-2-descent-map)
