---
article_id: af_223d5e1a47af6d3d8b268bce
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.CloudB3RC53.AppGEndpoints.unitSymbolF7_proof, ZInQ.Contrib.CloudB3RC53.AppGEndpoints.UnitSymbolF7
---

# (F.7): the units of the odd stage symbol

Let $\mathcal U$, the stages and the admissible sets be as on the page of [(F.6)](equation-f-6-odd-minimum.md),
let "simple zero" be a predicate and $j_{\rm gen}$ a function, and let $\delta_o$, $C_{\rm det}$ be integers
and $L$ a cutoff. Assume:

- $M_\theta\to\infty$ along $\mathcal U$;
- the visibility implication (O.8) of Appendix F (ELLIOT, with GLUE and PRINT inputs): an admissible
  $D$ with $v_2a_{M_\theta}(D)<M_\theta$ is a simple zero with
  $j_{\rm gen}(D)\le v_2a_{M_\theta}(D)+C_{\rm det}$;
- (F.6) at $\delta_o$ for every $W$.

Then for $\mathcal U$-many $\theta$: $M_\theta>\delta_o+L$, every admissible $D$ with $\omega(D)\le L$ has
$v_2a_{M_\theta}(D)\ge\omega(D)+\delta_o$, and if equality holds, then
$$\operatorname{ord}_{s=1}L(E^{(D)},s)=1,\qquad j_{\rm gen}(D)\le\omega(D)+C_o,\qquad
C_o=\delta_o+C_{\rm det}.\tag{F.7}$$

So on these stages the symbol $\mathcal A_{M_\theta,L}$ of [the overview](README.md) is the indicator of
equality in an inequality that always holds on the tested range, and its units satisfy (F.7). The constant
$C_o$ depends on neither $L$ nor the stage. The Lean statement does not define the symbol; it states
(F.7) for the equality case, and "simple zero" is the predicate supplied by (O.8).

The reduction of Theorem 5.3 does not use this theorem: at the final family, the simple zero and the
bound on $j_{\rm gen}$ come from (O.8) directly, in the proof of [Proposition
G.7](proposition-g-7-final-stage.md).

**Proof sketch.** For $\mathcal U$-many $\theta$ we have $M_\theta>\delta_o+L$ and (F.6) through weight
$L$. An invisible coefficient then has valuation at least $M_\theta>\delta_o+\omega(D)$, and a visible
one satisfies (F.6). At equality $v_2a_{M_\theta}(D)=\delta_o+\omega(D)<M_\theta$, so $D$ is visible
and (O.8) gives the simple zero and $j_{\rm gen}(D)\le\omega(D)+\delta_o+C_{\rm det}$.

## Depends on

- [Appendix G: the odd stage symbol](README.md)
- [(F.6): the attained odd minimum](equation-f-6-odd-minimum.md)

## Sources

- [Appendix G](../../../sources/manuscript.md#appendix-g)
