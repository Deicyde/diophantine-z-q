---
article_id: af_54aa6c42584ac758e6d1d56d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Kato812.finite_e1_812, ZInQ.Manuscript.RC.AppEK1.finite_e1, ZInQ.Manuscript.RC.AppEK1.constituentFactor, ZInQ.Manuscript.RC.Kato812.KatoZetaInterface812
---

# (E.1): the constituent identity at finite level

Assume Kato's retained-smoothed zeta elements for $E$ with the support-sensitive norm relation of his
Proposition 8.12 (`KatoZetaInterface812`, interface data: abstract Euler-system and Iwasawa data,
with `KatoProp812Print`, a draft transcription of Kato's Proposition 8.12 whose locator and
completeness are unverified; not an input of the reduction of Theorem 5.3), and two transfer laws for
the maps that carry Kato's classes to one constituent (hypotheses of the Lean theorem, not proved): the
map from the upper level factors through corestriction to the primitive level, and the primitive map is
semilinear for the weighted coefficient map of [(K10) and (E.2)](equation-k10-coefficient-map.md).

Let $E$ have newform level $N$, let $(h_x)$ be an admissible binary family at level $N$ with $F$ the
product of its primes, fix a constituent $x$ with $d=|h_x|$ and a level $n\ge1$, and take the smoothing
$c=d_s$ of [(K5)](equation-k6-smoothing-scalar.md) for $F$. Write $z_m$ for Kato's class at level $m$,
$\chi$ for a weight at level $d2^n$, and $E_q(\chi)$ for the image of Kato's Euler factor
$P_q(q^{-1}\sigma_q^{-1})$ under the weighted map, which is (K9). If $\Pi_{\rm up}$ and $\Pi_{\rm prim}$,
defined on the classes at levels $F2^n$ and $d2^n$, satisfy the two laws, then
$$\Pi_{\rm up}(z_{F2^n})=\prod_{q\mid F,\ q\nmid h_x}E_q(\chi)\cdot\Pi_{\rm prim}(z_{d2^n}).\tag{E.1}$$

The manuscript's identity is between actual classes after the cofinal limit,
$(Z_F)_x=\prod_{q\mid F/d}E_q(\chi_x)\,y_{2^\infty}$. Lean states it at each finite level, for abstract maps
that satisfy the two laws; the comparison of Kato's classes with actual Galois cohomology, which would
realize those maps, is a named obligation with no witness. A second Lean theorem gives the same
identity from any Euler-system data that has the norm relation at that level.

**Proof sketch.** The norm relation gives the corestriction of $z_{F2^n}$ to level $d2^n$ as the product of
the Euler factors at the unused primes times $z_{d2^n}$: the smoothing avoids the primes of the family,
and the primes of the level lie in both supports. Applying the primitive map, the factorization law and
semilinearity carry the product to $\prod E_q(\chi)$. There is no division by a group order.

In the Lean proof of Theorem 5.3 this theorem is not used: the construction of the retained class lives
inside the step `AppEFromKato` described in [the overview](README.md).

## Depends on

- [Appendix E: binary families](README.md)
- [(K10) and (E.2): the coefficient maps on group bases](equation-k10-coefficient-map.md)
- [(K5)–(K6): the retained smoothing and its central scalar](equation-k6-smoothing-scalar.md)

## Sources

- [Appendix E](../../../sources/manuscript.md#appendix-e)
