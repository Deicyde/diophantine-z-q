---
article_id: af_1e0e0658146106997fb754e8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.GlueSweep.Even.evenLowerBound_of_kato_ecurve, ZInQ.Manuscript.RC.GlueSweep.Even.evenLowerBound_of_appE_of_prints, ZInQ.Manuscript.RC.Even.evenLowerBound_of_evenScalar32, ZInQ.Manuscript.RC.Even.EvenLowerBound
---

# (E.9): the lower bound for $v_2L_*$

Assume [the cited results](../printed-results.md); Kato's construction of zeta elements for elliptic
curves without complex multiplication (`KatoZetaLeaf`, a printed result that is not an input of the
reduction of Theorem 5.3); that a rational CM $j$-invariant is an integer (`CMjInteger`, a reading of
the literature); and the construction of Appendix E on Kato's classes (`AppEFromKato`, the
manuscript's own step, not proved). The absolute convergence of $L(E,s)$ on $\operatorname{Re}s>3/2$, also a hypothesis of the Lean
theorem, is proved.

Let $\ell>0$, $E=E_\ell$, $N\ne0$, and fix a normalization $L_*$ of the central values of the quadratic
twists. Then there is a constant $C$ such that every odd squarefree $h$ with $L_*(h)\ne0$ satisfies
$$v_2L_*(h)\ge2\omega(h)+s(h)-C.\tag{E.9}$$

The manuscript's constant is $c_E+C_{\rm loc}$; the Lean constant is not split. The manuscript states
(E.9) for admissible $h$; in Lean every odd squarefree $h$ is admissible as a family of dimension zero.
A second Lean theorem gives (E.9) for any elliptic curve from the outputs of Appendix E (`AppEOutputs`)
and the cited results, without Kato's elements.

**Proof sketch.** By the forward rank-zero theorem (modularity, Kolyvagin and the Kummer sequence),
$L_*(h)\ne0$ gives Selmer corank zero. Apply (3.2) to the family with the single member $h$: the
clearing exponent gives $v_2u_h(0)\ge-C_{\rm ev}$, and the comparison in (3.2) turns this into the lower
bound. This is the manuscript's use of (E.5) and (E.8) with $G=1$.

In the Lean proof of Theorem 5.3 this theorem is not used.

## Depends on

- [The cited results](../printed-results.md)
- [Proposition 7.2: the fixed-form even scalar (3.2)](../section-7/proposition-7-2-even-scalar.md)

## Proof depends on

- [Proposition 7.2: the fixed-form even scalar (3.2)](../section-7/proposition-7-2-even-scalar.md)
- [(E.5): the uniform clearing of the even scalar](equation-e5-integrality.md)
- [(E.8): the central calibration of the even scalar](equation-e8-central-calibration.md)

## Sources

- [Appendix E](../../../sources/manuscript.md#appendix-e)
