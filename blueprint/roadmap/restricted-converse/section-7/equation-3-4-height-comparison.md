---
article_id: af_cffca754ab49bccd6570e79e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.CloudB3RC53.GenusOdd.genusLower34_of_artin, ZInQ.Contrib.CloudB3RC53.GenusOdd.GenusLower34
---

# (3.4): the height comparison

Assume [the cited results](../printed-results.md) and the Artin factorization of ring-class
$L$-functions (`ArtinFactorization`, which follows from the cited results and four fields of [the
remaining hypotheses](../remaining-hypotheses.md), `RCLeaves.artin`).

Let $E/\mathbb Q$ be an elliptic curve with $a_1=a_3=0$, $f$ its newform, a period lattice of $E$
without complex multiplication, and a scale $\kappa$ of the parametrization. Let $h_*$ be a genus
partner: a negative odd fundamental discriminant with $|h_*|>4$, in the squareclasses of $1$ at every
$p\mid2N$, with $L(E^{(h_*)},1)\ne0$ and $L_*(h_*)\in\mathbb Q$. Let $h$ be prepared (positive,
squarefree, a unit square at every $p\mid2N$, prime to $h_*$) with
$\operatorname{ord}_{s=1}L(E^{(h)},s)=1$, and let $k'$ be a companion of $h$ as in [Proposition
7.14](proposition-7-14-rough-companion.md), prime to $h_*$, with $L_*(hk')\ne0$. Then for every
genus Heegner datum (discriminant $hh_*$, conductor $1$) and every ring-class Heegner datum
(discriminant $k'$, conductor $|h|$, character $\chi_h$), both index valuations $j_{\rm gen}(h)$ and
$j_{\rm rc}(h,k')$ are finite and
$$2j_{\rm rc}(h,k')-2j_{\rm gen}(h)=v_2L_*(hk')-v_2L_*(h_*)+\epsilon,\qquad|\epsilon|\le2.\tag{3.4}$$

A Heegner datum is the analytic model of a Heegner point: a Heegner form, an embedding of the
ring-class field and a point mapping to the image of the CM point. The fixed period convention is the
same $\Omega^-$ on both sides, so no further constant appears. The rationality of $L_*(h_*)$, which the
manuscript takes for granted, is a hypothesis.

**Proof sketch.** The explicit Gross–Zagier formula of Cai, Shu and Tian applies twice, with all level
primes split, conductors prime to $N$ and the same parametrization. The Artin factorization splits each
ring-class $L$-function into two twists; the two Rankin products share the factor $L(E^{(h)},s)$.
Each rational free line has index at most two in its native rank-one lattice, which gives
$|\epsilon|\le2$.

In the Lean proof of Theorem 5.3, (3.4) at the companions and at the final $k$ comes from the cited
results, the Artin factorization and the genuine objects of the field `PreLeaves.odd_staged`
(`gz34Target_of_genusOdd`).

## Depends on

- [The cited results](../printed-results.md)
- [The remaining hypotheses](../remaining-hypotheses.md)
- [Proposition 7.14: a bounded companion (3.3)](proposition-7-14-rough-companion.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
