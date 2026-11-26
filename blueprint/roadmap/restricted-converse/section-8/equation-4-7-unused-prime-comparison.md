---
article_id: af_04ffb05ab611bbcc1f90da25
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Wiring.step47_of_naturalStep
---

# (4.7): the unused-prime comparison

Assume a triangular model over $F=\operatorname{Frac}\Lambda$ of one relaxation step at an unused odd prime
$q$ (`NaturalStep`, ELLIOT): its two-place block is built from the actual scalar Frobenius value $z$ at the
address, $a_q$, $q$ and a matrix $\mathrm{Fr}$ over $\mathbb Z_2$; its norm identity, functionals and basis
comparisons are part of the model. Assume separately that $\mathrm{Fr}$ has trace $a_q$ and determinant $q$
(`htr`, `hdet`, hypotheses of the theorem outside `NaturalStep`; for the actual Frobenius matrix on $T_2E$
they are proved, as in [Lemma 8.10](lemma-8-10-common-coordinate.md)). This is the form in which the field
`PostLeaves.common_coordinate` of [the remaining hypotheses](../remaining-hypotheses.md) supplies each
step.

Then, with $e_q=a_q-z-z^{-1}$ and $l_q$ the two-place quotient factor, the coordinates $u$ before and
$u'$ after relaxing $q$ satisfy
$$l_q\,u'=e_q^2\,\varepsilon_q\,u,\qquad\varepsilon_q\in\Lambda^\times.\tag{4.7}$$

The manuscript states (4.7) for the primitive and relaxed coordinates at one unused prime, in the original
integral determinant bases; the Lean statement is one step of a chain of relaxations, at one address, as an
identity in $F$. The docstring of the field records that the step models are existential and are met by
any coordinates satisfying (4.7), so the field asserts (4.7) at each step; this theorem fixes the shape of
the factors and the unit.

The reduction of Theorem 5.3 applies this theorem to the steps of the field, inside
[Lemma 8.10](lemma-8-10-common-coordinate.md): through `commonCoordinateTarget_of_L`, for the step
`RCSteps.common_coordinate` in `rcSteps_of_leaves` and again at the base.

**Proof sketch.** The quotient factor of the two-place block is the polynomial $l_q$, and the norm
identity gives the point factor $e_q$. The support triangle of the model relates the two coordinates: the
class contributes one $e_q$ through the norm identity, and the paired functional one more through the
restriction relation of the model's functionals (in the manuscript, naturality of the cup pairing, with
$e_q$ fixed by conjugation, which inverts $z$). The unit is $q^{-4}$ times the two basis comparisons, each a
$\Lambda$-unit.

## Depends on

- [The remaining hypotheses](../remaining-hypotheses.md)
- [Section 8: actual classes, local conditions and central comparison](README.md)

## Sources

- [Section 8](../../../sources/manuscript.md#section-8)
