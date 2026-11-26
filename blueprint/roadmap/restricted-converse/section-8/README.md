---
article_id: af_4c90f4845f75b4de32374ca4
---

# Section 8: actual classes, local conditions and central comparison

Section 8 builds the arithmetic objects behind the coordinates that the determinant argument of
Section 9 reads, for the final companion $k$ of [Section 7](../section-7/README.md) and
$K=\mathbb Q(\sqrt k)$, imaginary and split at $2N$. The finite coefficients are
$A_i=(\mathbb Z/2^i)[t]/(t^i)$ and $M_i=(T_2E\otimes A_i)(\chi_h\Psi_i)$, where $\Psi_i=(1+t)^{\xi_i}$
comes from a moving character. In order:

1. **Duality and local conditions.** Complex conjugation identifies the coefficients with their Tate
   dual and gives finite Selmer duality (Lemma 8.2). A finite Heegner descent over ring-class fields
   gives finite classes with one fixed multiplier $L$ (Proposition 8.3, with the norm relations (4.1)
   and the derivative step (4.2)). The local Kummer condition is its own annihilator (Lemma 8.4), and
   the support comparisons use the tame local model (4.4).
2. **The moving character** (Proposition 8.5): one character for the whole active list, with bounded
   trace valuations at the moving prime.
3. **The coordinate.** The retained class $z$ gives a closed paired functional $\lambda_z$
   (Proposition 8.6), and $[z]\otimes[\lambda_z]$ gives the coordinate $u$ (Definition 8.7).
4. **Central values.** Central specialization keeps the class (Lemma 8.8, with the retained boundary
   (4.5)); at known simple zeros $v_2u_{\rm prim}(0)$ is computed (Proposition 8.9, (4.6)); unused
   primes change the coordinate by an explicit factor (4.7), corrected by a unit (Lemma 8.10); and at the
   base the corrected coordinate vanishes when $L'(E/K,1)=0$ (Lemma 8.11).

The reduction of Theorem 5.3 takes (4.6), Lemma 8.10 (with (4.7) at each step) and Lemma 8.11 from
their theorems, in `rcSteps_of_leaves`. It also takes (4.6) at the companion pairs, for (3.5), directly
from the field `PreLeaves.eq35`, and it reaches the height-one clause of Proposition 8.6 through the
height-one regularity inputs (see [its page](proposition-8-6-paired-functional.md)). The other proved
items of the section are not inputs of the reduction.

## Definitions

**Conventions (Definition 8.1).** Sections 8 and 9 keep the fixed non-CM curve, its parametrization,
Tate lattice and old local types. Put $\Lambda=\mathbb Z_2[[t]]$ and $\mathscr O$ the completion of
$\Lambda_{(2)}$. A binary family uses one finite elementary abelian two-group $G$, one real sign and
common local squareclasses at $2N$, so its universal quadratic character is trivial at the real place
and at $2N$. Active primes are good odd primes split in $K$; the moving character is finite and trivial
at $2N$. The primitive and relaxed complexes use the actual Kummer, unramified, full and orthogonal
local conditions with their maps and homotopies, and every determinant coordinate uses the retained
integral determinant basis. In Lean the coordinates $u_{{\rm prim},x}$ and $\widetilde u_x$ of the final
families are interface data of [the remaining hypotheses](../remaining-hypotheses.md), constrained only
by their fields.

**The tame local model (4.4).** At a tame split prime the local free model has differentials
$d^0(v)=(Av,Cv)$ and $d^1(v,w)=-Cv+Dw$, with $A=\Phi-1$, $C=g-1$, $D=\Phi-N_q(g)$ and
$N_q(g)=\tfrac{q+1}2+\tfrac{q-1}2g$, so that $DC=CA$. At augmentation $g=1$ it splits into the
unramified complex $[\Phi-1]$ and the singular quotient $[\Phi-q]$; in Lean only the coefficients are
stated there: $N_q(1)=q$ for odd $q$ (`ZInQ.Manuscript.RC.Limits.normQ_one`), and in characteristic two
$C=0$ and $D=A$ (`ZInQ.Manuscript.RC.Limits.model_C_one_and_model_D_one_eq_model_A`). In Lean the model is
`ZInQ.Contrib.CloudB3RC53.PairedFunctional.tameComplex`, for any $A,C,D$ with $DC=CA$; at the moving
prime, `ZInQ.Manuscript.RC.Moving.moving_prime_DC_CA` checks $DC=CA$ in $A_i$ when
$r\equiv1\pmod{2^{i+1}}$.

**The class-functional coordinate (Definition 8.7).** For a constituent whose generic cohomology has
dimension one in degrees one and two and vanishes otherwise, $\det^{-1}C\simeq H^1(C)\otimes H^2(C)^*$,
and $u$ is the coordinate of $[z]\otimes[\lambda]$ in the retained integral determinant basis, with $z$ the
actual class and $\lambda$ the paired functional of Proposition 8.6. For a generically acyclic
constituent $u=0$. In Lean, `ZInQ.Manuscript.RC.Uniform.classFunctionalCoordWith` computes the
coordinate over a field (the generic fibre) from a complement, as
$\det[z\mid w]\,\lambda(y)/\det[Dw\mid y]$, independently of the complement, and
`ZInQ.Manuscript.RC.Central.isClassFunctionalCoord_zero_of_isUnit_det` gives $u=0$ in the acyclic case.
The reduction of Theorem 5.3 uses Definition 8.7 only through the fields `PreLeaves.eq35` (the
coordinates of its outer models), `PostLeaves.calibration` (the coordinate of its Kummer model),
`PostLeaves.clearing_model` and `PostLeaves.base_zero`.

## The items

- [Lemma 8.2: conjugate coefficients and finite Selmer duality](lemma-8-2-conjugate-duality.md)
- [Lemma 8.4: the derived Kummer condition is its own annihilator](lemma-8-4-local-kummer.md), with
  the Selmer cone (4.3)
- [Proposition 8.5: one moving character for the whole active list](proposition-8-5-moving-character.md),
  with (4.4a)–(4.4d)
- [Proposition 8.6: the paired functional and its integral representatives](proposition-8-6-paired-functional.md)
- [Lemma 8.8: central specialization keeps the same class](lemma-8-8-central-specialization.md)
- [(4.5): the retained boundary](equation-4-5-retained-boundary.md)
- [Proposition 8.9: arithmetic calibration at known simple zeros (4.6)](proposition-8-9-central-calibration.md)
- [Lemma 8.10: unused primes and one corrected coordinate](lemma-8-10-common-coordinate.md)
- [(4.7): the unused-prime comparison](equation-4-7-unused-prime-comparison.md)
- [Lemma 8.11: the base has zero coordinate if the derivative vanishes](lemma-8-11-base-zero.md)

Definitions 8.1 and 8.7 and the display (4.4), from the unnumbered passage on support comparisons, are
on this page because they are definitions: in Lean (4.4) is the complex `tameComplex`, and
`moving_prime_DC_CA` only checks $DC=CA$ at the moving prime. The display (4.6) is the conclusion of
Proposition 8.9 and shares its page.

## Items with no Lean statement

- **Proposition 8.3** (finite Heegner descent with one multiplier), with its displays (H1)–(H22), (4.1)
  and (4.2). No declaration states the proposition. Its steps are proved separately over abstract
  interfaces for the cohomology groups and Heegner points: for example
  `ZInQ.Manuscript.RC.HeegnerAlgebra.H7_assembled` (the derived class is invariant),
  `ZInQ.Manuscript.RC.HeegnerAlgebra.H11_assembled` (its descent with the multiplier $L$),
  `ZInQ.Manuscript.RC.HeegnerAlgebra.H19_assembled` (the singular coordinate at a derivative prime) and
  `ZInQ.Manuscript.RC.HeegnerAlgebra.eq42_assembled` ((4.2) from transported (H19)); the class at the base
  for $I=\varnothing$ is `ZInQ.Manuscript.RC.BaseZeroAssembly.classAtBase_of_construction`. The norm
  relations (4.1) are Theorem 2.15 of Cai, Chen and Liu. In Lean (4.1) itself is the predicate
  `ZInQ.Manuscript.RC.PrintsArith.HeegnerPointData.NormRelations`, which the zero system satisfies; the
  print is `ZInQ.Manuscript.RC.PrintsArith.CCLThm2_15AppliedWithUnits` (PRINT, applied through six GLUE
  identifications), which asks for points satisfying the relations weighted by the unit index
  (`NormRelationsWithUnits`) and an anchor. The print is not an input of the reduction. Its split clause
  at the base is asked inside `PostLeaves.base_zero`, as the field `SplitNormStage.hnorm` of each stage
  of the inner-limit data of [(4.5)](equation-4-5-retained-boundary.md) (PRINT), where it constrains
  nothing: the trivial stage meets it.
  The reduction of Theorem 5.3 takes what it needs of Proposition 8.3 from leaf fields: the
  conductor-one Heegner data and the stage boundaries of (4.5) at the base from `PostLeaves.base_zero`,
  and the valuations of the classes inside the Kummer model of `PostLeaves.calibration`.

## Remaining hypotheses that cover Section 8

These fields of [the remaining hypotheses](../remaining-hypotheses.md) cite lines of Section 8 in their
docstrings, with the kind each docstring gives:

- `PreLeaves.eq35` (ELLIOT and GLUE): the inputs of (3.5), including the calibration (4.6) at the
  companion pairs.
- `PostLeaves.companion` (derived from printed results, and a definition): the final $k$, which fixes
  $K=\mathbb Q(\sqrt k)$ at the start of the section.
- `PostLeaves.calibration` (ELLIOT, PRINT and GLUE): the inputs of (4.6); Proposition 8.9.
- `PostLeaves.common_coordinate` (definitions, GLUE and ELLIOT): the inputs of (4.7); Lemma 8.10.
- `PostLeaves.prim_regular` (ELLIOT and GLUE): height-one regularity, citing the coefficient modules
  $M_i$ and the base clause at Selmer corank one of Lemma 8.11.
- `PostLeaves.clearing_model` (ELLIOT and GLUE): the support comparisons (4.4) and Definition 8.7, for
  the full-condition identification of Section 9.
- `PostLeaves.base_zero` (ELLIOT, with PRINT and GLUE): Lemma 8.11 on the text's named steps, with the
  Heegner points and (4.1), the paired functional of Proposition 8.6, Definition 8.7, and the inner limit
  of (4.5) with the central comparison.

## Sources

- [Section 8](../../../sources/manuscript.md#section-8)
