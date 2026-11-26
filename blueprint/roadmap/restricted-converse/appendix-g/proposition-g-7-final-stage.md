---
article_id: af_77a133a0cd0a15bc665b535d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.CloudB3RC53.AppGEndpoints.finalFamily39_proof, ZInQ.Contrib.CloudB3RC53.AppGEndpoints.FinalFamily39, ZInQ.Contrib.CloudB3RC53.AppGEndpoints.AddressInput, ZInQ.Manuscript.RC.AddressGenuine.exists_family_realizesAt
---

# Proposition G.7: one actual stage for the final family

Let $\mathcal U$, the stages and the admissible sets be as on the page of [(F.6)](equation-f-6-odd-minimum.md);
let "prepared" and "simple zero" be predicates, $j_{\rm gen}$ and $L_*$ functions, $k$, $\delta_o$,
$C_{\rm det}$, $C_{e,\rm final}$ integers and $C_{\rm coarse}$ a rational number; and let binary families
be given with members $h_x$, $x\in\mathbb F_2^b$, and an admissibility predicate. Assume:

- $M_\theta\to\infty$ along $\mathcal U$;
- the visibility implication (O.8) of Appendix F (ELLIOT, with GLUE and PRINT inputs): an admissible
  $D$ with $v_2a_{M_\theta}(D)<M_\theta$ is a simple zero with
  $j_{\rm gen}(D)\le v_2a_{M_\theta}(D)+C_{\rm det}$;
- [(F.5)](equation-f-5-coarse-bound.md) at every stage with $C_{\rm coarse}$, and (F.6) at $\delta_o$
  for every $W$;
- the address input (`AddressInput`, ELLIOT): there is $b_0$ such that for every $b\ge b_0$ there
  are a budget $W_b$ and finitely many sets $A_1,\dots,A_t\in\mathcal U$ such that, at every stage in
  $A_1\cap\dots\cap A_t$ that is valid for the budget $W_b$ with $R=2$, some admissible family of
  dimension $b$ has, at every $x\ne0$: $\omega(h_x)\le W_b$, $h_x$ prepared and admissible at the stage,
  $v_2a_{M_\theta}(h_x)=\delta_o+\omega(h_x)$, $L_*(h_xk)\ne0$ and
  $v_2L_*(h_xk)\le2\omega(h_x)+C_{e,\rm final}$.

Then there is $b_0$ such that for every $b\ge b_0$ some admissible family of dimension $b$ has, at every
$x\ne0$, $h_x$ prepared and
$$\operatorname{ord}_{s=1}L(E^{(h_x)},s)=1,\quad L_*(h_xk)\ne0,\quad j_{\rm gen}(h_x)\le\omega(h_x)+C_o,
\quad v_2L_*(h_xk)\le2\omega(h_x)+C_e,$$
with $C_o=\delta_o+C_{\rm det}$ and $C_e=C_{e,\rm final}$, both fixed before $b$.

The families are generic in `FinalFamily39`. For the families of (3.9),
$h_x=\prod_{q\in Q}(q^*)^{\lambda_q(x)}$, the realization of the manuscript is `exists_family_realizesAt`:
every compatible typed graph over the alphabet of $K$-split classes, with nonzero activations, is realized
at every nonzero address by one admissible family, of distinct primes prime to the label modulus,
different from the theta prime and outside a given finite set, with the prescribed classes and residue
bits. The address construction of [Proposition G.6](proposition-g-6-simultaneous-address.md) and the
readings of both sources are packed into `AddressInput`.

The reduction of Theorem 5.3 takes (3.9) from [Proposition 7.17](../section-7/proposition-7-17-final-family.md)
(`finalFamilyTarget_of`), whose proof applies this theorem in `finalFamilyField_proof`, together with
`f6_of_isLeast` and `coarseF5_proof`; it derives the address input from the field
`PostLeaves.address` of [the remaining hypotheses](../remaining-hypotheses.md), with the realization from
`exists_family_realizesAt`.

**Proof sketch.** The stage choice of Proposition G.3 gives a set $B\in\mathcal U$ of stages valid for the
budget $W_b$ with $R=2$; then $B\cap A_1\cap\dots\cap A_t\in\mathcal U$ is nonempty. At a stage there the
address input gives the family, and $v_2a_{M_\theta}(h_x)=\delta_o+\omega(h_x)\le\delta_o+W_b<M_\theta$ by
the precision condition, so $h_x$ is visible and (O.8) gives the simple zero and
$j_{\rm gen}(h_x)\le\omega(h_x)+\delta_o+C_{\rm det}$.

## Depends on

- [Appendix G: visible coefficients and valid stages](README.md)
- [(F.5): the coarse lower bound on the odd coefficients](equation-f-5-coarse-bound.md)
- [(F.6): the attained odd minimum](equation-f-6-odd-minimum.md)
- [Proposition G.6: the address constructions](proposition-g-6-simultaneous-address.md)
- [The remaining hypotheses](../remaining-hypotheses.md)

## Sources

- [Appendix G](../../../sources/manuscript.md#appendix-g)
