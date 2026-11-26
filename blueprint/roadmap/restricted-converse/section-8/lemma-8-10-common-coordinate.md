---
article_id: af_b57b34473e2290b993a8988e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Wiring.commonCoordinateTarget_of_NF, ZInQ.Manuscript.RC.Wiring.CommonCoordinateTarget, ZInQ.Manuscript.RC.Wiring.CommonCoordinateTrianglesL.corrected_eq
---

# Lemma 8.10: unused primes and one corrected coordinate

Assume the field `PostLeaves.common_coordinate` of [the remaining hypotheses](../remaining-hypotheses.md)
(definitions, GLUE and ELLIOT): $E_\ell$ is elliptic, a coefficient datum is fixed (a number field, a set of
its primes outside which $E[2^\infty]$ is unramified; GLUE Néron–Ogg–Shafarevich), and at every address
$x$ of a final family the graph primes are good, the class-functional coordinates relaxed at the subsets of
the unused primes $U_x$ lie in $F=\operatorname{Frac}\Lambda$, the primitive one is regular at $t=0$ with
$t$-expansion $u_{{\rm prim},x}$, each relaxation step at an unused prime has a triangular model over $F$
built from the actual Frobenius matrix on $T_2E$ (its trace $a_q$ and determinant $q$ are proved), and the
product $\widetilde u_x=\eta_xu_{{\rm rel},x}$ is regular with $t$-expansion $\widetilde u_x$.

Then for every family of [(3.9)](../section-7/proposition-7-17-final-family.md) and every address $x$,
$$\widetilde u_x=\varepsilon_x\,u_{{\rm prim},x},\qquad\varepsilon_x\in\Lambda^\times,$$
as power series, and the same identity holds in $F$ before $t$-expansion (`corrected_eq`).

Here $\eta_x=\prod_{q\in U_x}l_q/e_q^2$ is a definition, evaluated in $F$, where it may have a pole at
$t=0$; only the product is specialized. The universal correction is defined in $\mathscr O[G]$, so the
manuscript's integrality of $\eta$ is built in rather than proved. The docstring of the field records that,
for $\ell>0$ and a support containing $\{2,3\}$ and the primes of $\ell$, the field is equivalent to (4.7)
at each step, $\varepsilon_x=1$ where no graph prime is unused, and $u_{{\rm prim},x}\in F$; its step models
are existential and not tied to the actual Selmer complexes, and its coefficient datum is existential (the
manuscript's is $K=\mathbb Q(\sqrt k)$). The field is also asked in the branch where the odd symbol is a
unit at the empty configuration.

The reduction of Theorem 5.3 uses this theorem in `rcSteps_of_leaves` for the step
`RCSteps.common_coordinate`, and that step again in the height-one regularity of Section 9
(`heightOneTarget_of_HPK`). It uses the statement once more at the base in
[Lemma 8.11](lemma-8-11-base-zero.md), inside `baseZeroTarget_of_LF`, through
`commonCoordinateTarget_of_L` (which this theorem wraps) rather than through this theorem.

**Proof sketch.** At each unused prime, [(4.7)](equation-4-7-unused-prime-comparison.md) relates the
coordinates before and after relaxing it, with a $\Lambda$-unit. Relaxing the primes of $U_x$ one at a time
gives $(\prod_{q}l_q)\,u_{{\rm rel},x}=(\prod_qe_q^2)\,E\,u_{{\rm prim},x}$ with $E\in\Lambda^\times$, so
$\eta_xu_{{\rm rel},x}=E\,u_{{\rm prim},x}$ in $F$: the poles of $\eta_x$ cancel. Uniqueness of
$t$-expansions turns this into the identity of power series.

## Depends on

- [The remaining hypotheses](../remaining-hypotheses.md)
- [Section 8: actual classes, local conditions and central comparison](README.md)
- [Proposition 7.17: one family for the two coefficient tests (3.9)](../section-7/proposition-7-17-final-family.md)

## Proof depends on

- [(4.7): the unused-prime comparison](equation-4-7-unused-prime-comparison.md)

## Sources

- [Section 8](../../../sources/manuscript.md#section-8)
