---
article_id: af_e71ff3e7bc043aee61761d57
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Wiring.baseZeroTarget_of_LF, ZInQ.Manuscript.RC.Wiring.BaseZeroTarget
---

# Lemma 8.11: the base has zero coordinate if the derivative vanishes

Assume [the cited results](../printed-results.md) (the conductor-one height formula of Cai, Shu and Tian)
and three hypotheses that the reduction of Theorem 5.3 derives from fields of [the remaining
hypotheses](../remaining-hypotheses.md):

- `BaseZeroAssembly.BaseZeroLeafInputs`, from the field `PostLeaves.base_zero` (ELLIOT, with PRINT and
  GLUE for the Heegner data) and the Artin factorization (`RCLeaves.artin`): the conductor-one Heegner
  data, a two-term model of the primitive complex at the base with its retained cycle, the central
  comparison with the Selmer groups of $E$ and $E^{(k)}$, the pairing and chain map defining the paired
  functional, the coordinate statement of Definition 8.7, and the inner-limit data of
  [(4.5)](equation-4-5-retained-boundary.md) at the base;
- `CommonCoordinateInputsLF`, from the field `PostLeaves.common_coordinate`, as in
  [Lemma 8.10](lemma-8-10-common-coordinate.md);
- `PrimRegularityInputs`, from the field `PostLeaves.prim_regular` (ELLIOT and GLUE; Section 9).

Let $k$ be the final companion and $K=\mathbb Q(\sqrt k)$. Suppose $E$ has full two-primary Selmer corank
one over $K$, $L(E^{(k)},1)\ne0$ and $\operatorname{ord}_{s=1}L(E,s)L(E^{(k)},s)\ge2$, that is
$L'(E/K,1)=0$. Then for every family of [(3.9)](../section-7/proposition-7-17-final-family.md), whose base
is $h_0=1$, the corrected coordinate vanishes at the centre: $\widetilde u_0(0)=0$.

The Selmer group over $K$ is not defined in Lean: its corank one is stated as corank one for
$\operatorname{Sel}_{2^\infty}(E/\mathbb Q)$ and corank zero for $\operatorname{Sel}_{2^\infty}(E^{(k)}/\mathbb Q)$,
the identity the manuscript proves with the sum and difference isogenies. The manuscript also concludes
$u_{{\rm prim},0}(0)=0$ and proves regularity at $(t)$ by a local argument;
the Lean statement concludes only $\widetilde u_0(0)=0$, and regularity comes from the Section 9 field
`PostLeaves.prim_regular`. The docstrings record that the field `PostLeaves.base_zero` is conclusion-shaped:
for a torsion specified point its core is equivalent to "$u_{{\rm prim},0}$ is regular at $(t)$ and
vanishes at $0$", and its matrix model, cocycle and chain map are not tied to the actual primitive complex,
class and orthogonal comparison.

The reduction of Theorem 5.3 uses this theorem in `rcSteps_of_leaves` for the step `RCSteps.base_zero`.

**Proof sketch.** From the field, the Lean proof derives the central rank of the model from the Selmer
hypothesis, the specialization of the cycle from the inner-limit data of (4.5), and the closedness of the
paired functional from the Leibniz identity. The height formula makes the specified point torsion when
$L'(E/K,1)=0$, so the central cycle is zero. Over the discrete valuation ring $\Lambda_{(t)}$ the generic and
central dimensions agree, so the coordinate of the cycle and functional specializes to that of their
central tensor, which is zero. Finally $\widetilde u_0=\varepsilon_0u_{{\rm prim},0}$ with
$\varepsilon_0\in\Lambda^\times$ by Lemma 8.10.

## Depends on

- [The cited results](../printed-results.md)
- [The remaining hypotheses](../remaining-hypotheses.md)
- [Section 8: actual classes, local conditions and central comparison](README.md)
- [Proposition 7.17: one family for the two coefficient tests (3.9)](../section-7/proposition-7-17-final-family.md)

## Proof depends on

- [Lemma 8.10: unused primes and one corrected coordinate](lemma-8-10-common-coordinate.md)

## Sources

- [Section 8](../../../sources/manuscript.md#section-8)
