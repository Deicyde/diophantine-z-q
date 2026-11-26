---
article_id: af_daef972a8378bf6ef9a0e555
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.CloudB3RC53.AppGEndpoints.coarseF5_proof, ZInQ.Contrib.CloudB3RC53.AppGEndpoints.CoarseF5, ZInQ.Manuscript.RC.Wiring.coarseF5_of_leaves
---

# (F.5): the coarse lower bound on the odd coefficients

Fix one stage, of precision $M$, with odd coefficients $a_M(D)$, and let "admissible" and "simple zero" be
predicates, $j_{\rm gen}$ and $s\ge0$ functions and $C_{\rm det}$, $C_{\rm gen}$ integers. Assume:

- the visibility implication (O.8) of Appendix F (ELLIOT, with GLUE and PRINT inputs): an admissible
  $D$ with $v_2a_M(D)<M$ is a simple zero, $\operatorname{ord}_{s=1}L(E^{(D)},s)=1$, with
  $j_{\rm gen}(D)\le v_2a_M(D)+C_{\rm det}$;
- (F.4) at the admissible simple zeros: $2j_{\rm gen}(D)\ge2\omega(D)+s(D)-C_{\rm gen}$.

Then every admissible $D$ satisfies
$$v_2a_M(D)\ge\min\{M,\ \omega(D)-C_{\rm coarse}\},\qquad C_{\rm coarse}=C_{\rm gen}/2+C_{\rm det}.\tag{F.5}$$

(F.4) is the inequality [(3.6)](../section-7/equation-3-6-genus-lower-bound.md); in the manuscript it
applies because admissible theta parameters lie in the prepared filter. The valuation of a zero
coefficient is $+\infty$, and $C_{\rm coarse}$ may be a half-integer.

Over the interface data of [the remaining hypotheses](../remaining-hypotheses.md), `coarseF5_of_leaves`
gives one $C_{\rm coarse}$ for which (F.5) holds at every admissible $D$ of every stage. Its hypotheses
are (3.3) and (3.4) at the companions, (3.5), (O.8) and the GLUE that admissible theta parameters are
prepared; it obtains (F.4) from (3.6). It is not on the reduction path: its callers,
`oddStageSource_of_leaves` and `coarse_on_filter` (with the rest of `AppGCoarse`), are not used by the
reduction. The reduction of Theorem 5.3 repeats the computation inside `exists_oddMinimum` and
`finalFamilyField_proof`, which apply `coarseF5_proof` in the proofs of the attained odd minimum
([(F.6)](equation-f-6-odd-minimum.md)) and of (3.9).

**Proof sketch.** If $v_2a_M(D)\ge M$ there is nothing to prove. Otherwise $D$ is visible, so (O.8)
makes it a simple zero with $j_{\rm gen}(D)\le v_2a_M(D)+C_{\rm det}$, and (F.4) with $s(D)\ge0$ gives
$2v_2a_M(D)\ge2\omega(D)-C_{\rm gen}-2C_{\rm det}$. A visible coefficient is used only after (O.8) has
given its simple zero, so no future minimum enters.

## Depends on

- [(3.6): the genus lower bound](../section-7/equation-3-6-genus-lower-bound.md)
- [The remaining hypotheses](../remaining-hypotheses.md)

## Sources

- [Appendix G](../../../sources/manuscript.md#appendix-g)
