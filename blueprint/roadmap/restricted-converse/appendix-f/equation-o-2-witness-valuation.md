---
article_id: af_809f68bd769e04334dc6243c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Wiring.OddStagedInstance.witnessValuation, ZInQ.Manuscript.RC.Stages.witnessValuation_withStages, ZInQ.Manuscript.RC.Visibility.WitnessValuation
---

# (O.2): the stage valuation at the fixed witness

Let $E=E_\ell$, $h_*$ the genus partner and $L$ the fixed multiplier. Assume the staged odd data
(`OddStagedInstance`), of which the theorem uses:

- $E$ and $A=E^{(D_w)}$ are elliptic curves (`eE`, `eA`; definitions);
- the fixed witness $D_w$ in the prepared filter with its selected genus datum (definitions);
- an exact witness: a rational point $R$ of $A=E^{(D_w)}$ whose twist is $LP_{D_w}$ (ELLIOT);
- the detector outputs at $Q=R$ (ELLIOT): compatible $2$-power division points of $Q$ with Kummer
  cocycle $c_Q$, an element $\sigma\in G_{\mathbb Q}$ with $\sigma^2$ trivial on $T_2E$, a
  $\mathbb Z_2$-linear row $b$ on $T_2A$ with $b(c_Q(\sigma^2))=2^{a+1}$, and an actual detecting
  sequence of primes $\ell_0$ with selected Frobenius elements;
- the stages of the data are the construction at that sequence, with precision
  $M_\theta=a+2+\theta$ (definitions);
- at the selected datum of $D_w$ the stage map is the actual map: reduction at the place of the
  selected Frobenius element, the finite Kummer map $\kappa_M(P)=F^2R'-R'$ for $2^MR'=P$, the inverse
  torsion specialization through the twist, and the row $b$, so that $\lambda_M=b\circ\kappa_M$
  (definitions).

Then on a set of stages in the ultrafilter (the proof gives every stage) $D_w$ is admissible and, with
$c_w=a+1$,
$$v_2\lambda_{M_\theta}(\overline Q)=c_w<M_\theta.\tag{O.2}$$

The valuation is read on the integer lift $\lambda_\theta(D_w)\in[0,2^{M_\theta})$ of
$\lambda_{M_\theta}(\overline{LP_{D_w}})$: `WitnessValuation` asserts admissibility and this exact
valuation. The inequality $c_w<M_\theta$ is not in the conclusion (it is in `WitnessO2At`, the printed
form); it follows from $M_\theta=c_w+1+\theta$ (`StagesFrom.Mθ_eq`), and with it this is the valuation
in $\mathbb Z/2^{M_\theta}$. The other assertions of Proposition F.1 about $\lambda_M$
(additivity, surjectivity, Frobenius sign $+1$) and the existence of $h_*$, $D_w$ and $L$ are not part
of the theorem. The existence of the detector outputs, given Serre's open image theorem, is
[(3.7)](../section-7/equation-3-7-advanced-stages.md); the reduction does not use it.

In the reduction of Theorem 5.3 the staged data are the field `PreLeaves.odd_staged` of [the
remaining hypotheses](../remaining-hypotheses.md), and (O.2) at the witness is this theorem, through
`OddStagedInstance.toOddInstance`; with (O.7) it gives the fixed visible witness of Section 7,
$v_2a_\theta(D_w)=9+\omega(N)+c_w$, where $9=v_2c_0$.

**Proof sketch.** The specialization identity (`WitnessSpecialization`) says that at the selected
datum the stage map applied to $LP_{D_w}$ is the row $b$ applied to $c_Q(g^2)$ at level $M_\theta$,
where $g$ is the selected Frobenius element; it follows from the actual stage map by good reduction
at that place. Since $g$ agrees with $\sigma$ on the field of $2^{M}$-division points of $Q$,
$c_Q(g^2)\equiv c_Q(\sigma^2)$ modulo $2^{M}$, so the value is the residue of $2^{a+1}$, whose
canonical lift has valuation exactly $a+1$ because $a+1<M_\theta$.

## Depends on

- [(O.1): the conductor-one point](equation-o-1-genus-point.md)
- [(3.7): arbitrarily advanced stages](../section-7/equation-3-7-advanced-stages.md)
- [The remaining hypotheses](../remaining-hypotheses.md)

## Sources

- [Appendix F](../../../sources/manuscript.md#appendix-f)
