---
article_id: af_d4dfcf1a949ae256164c4607
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.CloudB3RC53.AppGEndpoints.oddMinimumF6_proof, ZInQ.Contrib.CloudB3RC53.AppGEndpoints.OddMinimumF6, ZInQ.Contrib.CloudB3RC53.AppGEndpoints.f6_of_isLeast, ZInQ.Manuscript.RC.Wiring.exists_oddMinimum
---

# (F.6): the attained odd minimum

Let $\mathcal U$ be an ultrafilter on the stages $\theta\in\mathbb N$, with precisions $M_\theta$, odd
coefficients $a_{M_\theta}(D)$ and an admissible set at each stage. Assume:

- (F.5) at every stage, with one constant $C_{\rm coarse}$;
- a fixed visible witness (ELLIOT, with PRINT Bump–Friedberg–Hoffstein, Cai–Shu–Tian and Serre, and
  GLUE Chebotarev): an index $D_w$ and an integer $c$ such that, for $\mathcal U$-many $\theta$, $D_w$
  is admissible and $v_2a_{M_\theta}(D_w)=c<M_\theta$.

Then the depth set of [the overview](README.md) has a least element $\delta_o$, and for every $W$, for
$\mathcal U$-many $\theta$,
$$v_2a_{M_\theta}(D)\ge\omega(D)+\delta_o\quad\text{for every visible admissible }D\text{ with }
\omega(D)\le W.\tag{F.6}$$

`f6_of_isLeast` gives (F.6) from (F.5) at any least element of the depth set. Over the interface data of
[the remaining hypotheses](../remaining-hypotheses.md), `exists_oddMinimum` gives the least element from
(3.3) and (3.4) at the companions, (3.5), (O.8), the GLUE that admissible theta parameters are prepared,
and the fixed witness (`WitnessLeaf`). The manuscript has the witness at every stage with $M_\theta>c$,
from (3.7), (O.2) and (O.7); the Lean statement needs it only on a set in $\mathcal U$, and does not use
$M_\theta\to\infty$.

In the reduction of Theorem 5.3 the odd minimum $\delta_o$ is the least element given by
`exists_oddMinimum`, which applies `oddMinimumF6_proof`, with the witness derived from the field
`PreLeaves.odd_staged`. (F.6) at $\delta_o$ is taken from `f6_of_isLeast` in `finalFamilyField_proof`,
the proof of (3.9), which also applies `finalFamily39_proof` and `coarseF5_proof`.

**Proof sketch.** On a visible coefficient (F.5) gives $v_2a_{M_\theta}(D)-\omega(D)\ge-C_{\rm coarse}$,
so the depth set is bounded below, and the witness puts $c-\omega(D_w)$ in it; so it has a least element
$\delta_o$. If (F.6) failed for some $W$, choose a violating $D_\theta$ at $\mathcal U$-many stages. Its
depth is one of the finitely many integers from $-C_{\rm coarse}$ to $\delta_o-1$, so one of them occurs
on a set in $\mathcal U$ and lies in the depth set, below $\delta_o$.

## Depends on

- [Appendix G: visible coefficients and the odd minimum](README.md)
- [(F.5): the coarse lower bound on the odd coefficients](equation-f-5-coarse-bound.md)
- [The remaining hypotheses](../remaining-hypotheses.md)

## Sources

- [Appendix G](../../../sources/manuscript.md#appendix-g)
