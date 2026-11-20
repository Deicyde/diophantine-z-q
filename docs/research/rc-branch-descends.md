# Scoped CM field of definition from modular-function values

**Result.** At every nonzero level `N`, `cmFieldOfDefinitionScoped_of_values` gives
`CMFieldOfDefinitionScoped (X0Branch.model N)` from the single input
`HeegnerValuesInRingClassField N`. The bridge uses the residue field at the image
of the complex point on the normalized model. It needs neither a plane equation
near that image nor a denominator that is nonzero in a particular presentation
in terms of the two j-functions. At level one, `cmFieldOfDefinitionScoped_one_of_values`
gives the same proposition that the independent singular modulus proof establishes
as `CMScope.cmFieldOfDefinitionScoped_one`. The general-level input is **GLUE until
read**. No reciprocity theorem is proved or installed as an axiom.

The local ring at the image of a complex point embeds into the function field.
Its elements are the rational functions regular at that image. Each element
comes from a section on some neighborhood. The model's existing
`X0Model.sectionGerm` theorem identifies the value of such a section with the
finite limit of the corresponding meromorphic modular function. Evaluation
then factors through the residue field, and the quotient map onto the residue
field is surjective. Thus the embedded residue field is precisely the set of
these values. If they all lie in the image of one embedding of `H`, the
residue field map into ℂ factors through `H`. Composing the spectrum of that
factor with the canonical map from the spectrum of the residue field gives the
desired point. Base change along the same embedding recovers the original
complex point. The argument works even without a separate closedness proof for
the image on the rational model.

At level one the finite chart is the affine j-line:
`CMField2.finitePointEval_one_mem_range` checks every finite-chart evaluation
from the one j-value. The new route supplies all germs directly and gives the
same normalized curve and the same complex uniformization. It makes no
comparison between the existentially chosen embeddings in the two proofs.

## Declarations

Names in this table are under `ZInQ.Manuscript.RC.BranchDescends`.

| Declaration | Statement and the input it supplies |
| --- | --- |
| `HeegnerValuesInRingClassField N` | For exactly the field, conductor, and oriented form data of `CMFieldOfDefinitionScoped`, there is an embedding `ι : H →ₐ[ℚ] ℂ` such that every `g ∈ ℚ(j,j_N)` with finite germ at `τ = cmPoint A B d` has its value in `Set.range ι`. Supplies the only printed input. |
| `residueField_range_eq_stalkValue_range` | For a complex point on any scheme, the range of the induced residue field embedding into ℂ equals the range of the evaluation map from the stalk into ℂ. Supplies generation by local values (c). |
| `fieldPoint_of_stalk_values` | For `x : FieldPoint p ℂ` and `ι : H →ₐ[ℚ] ℂ`, if every value from the stalk at the image of `x` lies in the range of `ι`, then `∃ y : FieldPoint p H, y.map ι = x`. Supplies descent for the given embedding (c). |
| `sectionMap_eq_germ_evaluation` | On an open containing the image of a complex point, section pullback to ℂ equals passing to the stalk germ and evaluating it. Supplies the section-to-stalk comparison (c). |
| `stalkValue_is_modularValue` | For every local function at the image of the normalized model's point at `τ`, the meromorphic germ of its function field image is finite, and its value equals the algebraic evaluation. Supplies eligibility for the analytic print, including at the two branches in the level-two example (c). |
| `cmFieldOfDefinitionScoped_of_values` | `HeegnerValuesInRingClassField N → CMFieldOfDefinitionScoped (X0Branch.model N)` for `[NeZero N]`. Supplies the scoped source point (c). |
| `cmFieldOfDefinitionScoped_one_of_values` | The same implication at `N = 1`, with the same model as the inherited unconditional proof (c). |

## Remaining hypothesis and owner

| Remaining hypothesis | Owner | Scope relative to (O.7) |
| --- | --- | --- |
| `HeegnerValuesInRingClassField N`, at the level in use | Shared CM source descent; the reading desk checks the print | One ring class field per specified CM point and only scalar values of rational modular functions finite there. There is no elliptic image, trace, weighted theta coefficient, choice of phase, or Kummer comparison. It supplies one strictly smaller part of the construction than the comparison at tex 9105–9116; this is a scope comparison, not a claim that (O.7) implies CM reciprocity. |

No separate branch, smoothness, residue field, CM point, or lattice comparison
hypothesis is passed to the concluding theorem. Level positivity is the model's
existing `NeZero N` parameter; the arithmetic and orientation guards are the
quantified domain of the input. Consumer hypotheses are outside this result.

The input talks about finite analytic values of modular functions. It has no
quantifier over scheme points or lifts, and its conclusion is a field membership,
not an equality of scheme morphisms. The bridge proves why this value data
suffices. In the standard value form of reciprocity, apply the formula to the
functions for the subgroup preserving the cyclic level structure. For these
Heegner data the two proper lattices have the same order, and multiplication by
a local unit of the order preserves the lattice pair. The reciprocity action of
those units therefore fixes the values for the rational coefficient subfield.
In the class-field description the unit stabilizer gives the ring class field.
This takes only the containment clause for the prescribed functions (and its
single common field); it discards the Artin action, any generation statement,
and norm relations. This describes the specialization to check against the
printed hypotheses. A formula giving values just in a ray class field does
not by itself supply the stated containment.

## Page check for the reading desk

- **Shimura, _Introduction to the Arithmetic Theory of Automorphic Functions_
  (1971), Ch. 6, Thm. 6.31 and the following CM results — UNVERIFIED.**
  Transcribe the exact finite-value statement, including the field containing
  the values. If only an Artin action or ray class containment is stated, locate
  the ring class specialization for the stabilizer of the cyclic subgroup.
  Distinguish “finite at this CM argument” from “holomorphic everywhere on
  the upper half-plane.”
- **Gross, _Heegner points on X₀(N)_ (1984), §1 — UNVERIFIED.**
  Transcribe the order and pair of lattices used and check whether the section
  gives the value assertion or only the point and ideal class formulation.
  If it only gives points, record it as corroboration of the setting; it does
  not supply the requested value-form citation on its own.
- In each source record whether the order may be nonmaximal, whether its
  conductor must be prime to the level, and the exact Heegner splitting or
  congruence hypothesis (including the role of 2). The Lean binder explicitly
  retains `c.Coprime (2 * N * (discr K).natAbs)` and the hypotheses of the
  scoped field statement. A maximal-order-only clause covers just `c = 1`;
  record it as such and leave nonmaximal orders unverified until the correct
  passage is found.
- Check the coefficient field and the subgroup convention together.
  `ModularCurve.modularFunctionField N` is the subfield generated by the
  rational Laurent expansions of `j(τ)` and `j(Nτ)` at infinity. Match the
  cyclic subgroup generated by `1/N` in the chosen lattice and the rational
  coefficient restriction if the source uses the full level field with
  cyclotomic coefficients. Confirm the field for all finite values is the ring
  class field in one embedding fixed for the point, as in the printed input.

## Known issues

- Tex 2915–2916 gives no citation for the field of definition. Its nearby
  Cai–Chen–Liu citation at tex 2918 is for the curve and trace comparison;
  the applicable value-form passage remains unverified. No new error in
  the manuscript or in a source was established.
- The symbol `d` at tex 2915 is the order's conductor. In Lean `c` is the
  conductor and `d` is the order discriminant. Coprimality to `2N |D_K|`
  is retained from tex 2841; the nearby `(d,N)=1` in tex 2919 does not replace it.
- `CMField2.levelTwo_coordinates` and `CMField2.levelTwo_distinct` show that
  the forms `[2,1,1]` and `[2,-1,1]` of discriminant −7 give the same pair
  of plane coordinates and different normalized points. Both lie in the
  scoped conductor-one family, with their respective orientations. This
  disproves point determination from the pair; it is not a counterexample
  to ring class descent.

## Manuscript check

| Tex lines | Verdict | Check |
| --- | --- | --- |
| 2839–2840 | OK | The field is imaginary quadratic and split at the primes of `2N`; the two exceptional fields are excluded. |
| 2841–2844 | OK | The conductor is positive and prime to `2N D_K`; its order and ring class field are the ones used in the input. |
| 2915–2916 (lattices and orientations) | OK | The pre-existing lattice comparison identifies the oriented primitive form with the proper lattice pair: `CMField2.formIdeal_scaled_eq_levelInverse_mul`. Only the individual point enters this proof. |
| 2915–2916 (field of definition) | gap filled | The normal model's residue field gives a proved bridge from value containment to the point. The single printed value statement still needs the page check above. |
| 2917 | OK | The image under the stated rational map follows once the source point descends; the consumer is outside this lane. |
| 2918–2919 | unverified | The cited curve identification and reduction of the condition in Cai–Chen–Liu, Thm. 2.15 (UNVERIFIED), are not needed for this proof. |

## Verification

See the [results log](../../scratch/rc-branch-descends/log.md).

The imports built offline. All three deliverable files passed serial
`lake env lean -j1` with `MemoryMax=60G`; the build gate checked load and
available memory before each compiler invocation. The standalone
[scratch check](../../scratch/rc-branch-descends/Check.lean) passed. The result
of each `#print axioms` command was exactly
`[propext, Classical.choice, Quot.sound]`:

- `HeegnerValuesInRingClassField`
- `residueField_range_eq_stalkValue_range`
- `fieldPoint_of_stalk_values`
- `sectionMap_eq_germ_evaluation`
- `stalkValue_is_modularValue`
- `cmFieldOfDefinitionScoped_of_values`
- `cmFieldOfDefinitionScoped_one_of_values`
