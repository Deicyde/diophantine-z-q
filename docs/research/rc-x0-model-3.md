# Normalized branches of X₀(N) and the O.7 reduction

**General-level model.** `X0Model3.exists_stabilizer_germ_match` proves
exactly the normalized branch comparison specified in
`docs/research/rc-x0-model-2.md`, for every nonzero level, including
elliptic centers. `X0Model3.complexPoint_eq_iff` and `X0Model3.model`
give the orbit classification and the complete `PreparedParam.X0Model N`
on the prescribed rational normalization. There is no additional input
for this model.

**O.7 scoped stop.** On a source CM point at the embedding of the
selected datum, the fixed-scale rational parametrization evaluates to
the datum's chosen point over its field. The same holds for each Artin
conjugate, also after applying the exact stage reduction. Thus `hπ`
reduces to identifying the PM special-fibre map with the specialization
of this rational parametrization on the indicated coarse points. The
extension and its identification with the PM map at the same place
are the uncited good-reduction input of tex 8476–8479 (ELLIOT).
The current PM input types do not encode that identification.

The branch proof is ported from commit `398868586`, already used by
the fixed-scale parametrization branch, under the new namespace so this
base needs no merge or changes to existing files. It is on the spot,
provenance (c). The port uses the same curve, rational structure map,
field, chart and expansion as that parametrization. Its structure
fields have the same data; the proof fields do not affect that
identification. For integration, one copy of the comparison suffices.

## Normalized branch comparison

Each valuative lift has a generic point given by the field embedding
determined by the two modular germs, and a special point given by their
valuation residue. Pullback of any regular section gives the
corresponding holomorphic germ. Around a chart point the finite affine
j-chart allows these germs to be recovered as evaluations at the nearby
valuative points: basic opens are nonvanishing loci, and finitely many
generators allow the evaluations to be compared with their
meromorphic continuations simultaneously.

At the common normalized point choose an affine neighborhood with
one étale coordinate, using smoothness of relative dimension one.
For two nearby evaluations agreeing on that coordinate, evaluate the
complement of the idempotent generating the diagonal ideal of the
relative tensor square. It is one at the shared center. Continuity
keeps it nonzero, so its annihilation of the diagonal ideal makes the
two evaluations agree on every section. Neither pullback of the étale
coordinate is locally constant: otherwise this uniqueness, applied
with the other parameter fixed at the center, would force the first
projection to be locally constant. Proper discontinuity and the
j-orbit theorem show that the local j-fibre of the center consists of
the center alone.

The holomorphic open mapping theorem supplies punctured overlap of
the two normalized lifts, with the second parameter in any prescribed
neighborhood. Their j-coordinates agree by projection. Their second
coordinates agree by evaluating the same ratio of regular sections,
with nonzero denominator near the punctured centers. Proper
discontinuity restricts any nearby j-coordinate match to the finite
center stabilizer. One of those reparametrizations then matches
recurrently, and the analytic identity principle gives equality of its
punctured second-coordinate germs. This uses the smooth curve and its
valuative lifts, so coincident plane points cause no ambiguity.

## Statements

The declarations below are in `ZInQ.Manuscript.RC.X0Model3`.
`P_N` is `X0Model.complexPoint N` and `J_N` is
`X0Model.analyticJN N`. A punctured germ in these statements is
at the complex coordinate of the center.

| File | Theorems and what they supply |
| --- | --- |
| `Unramified.lean` | `pairEval_tmul` evaluates a pure tensor as the product of the evaluations when both maps agree on the base; `pairEval_self` reduces evaluation with both maps equal to evaluation after multiplication. `continuousPairTest` represents any tensor evaluation by a function continuous at the pair of parameter centers. `eventually_eq_of_unramified` gives neighborhoods of two parameter centers with one common evaluation on an essentially finite type formally unramified algebra: inside them, evaluations agreeing on the base agree everywhere. |
| `AffineEval.lean` | `affineEval_factor` reconstructs the point in an affine open from its section evaluation; `affineEval_congr` and `affineEval_injective` compare equality in both directions. `mem_basicOpen_iff_eval_ne_zero` identifies basic-open membership with nonzero evaluation; `finiteChart_affine` and `chart_mem_finiteChart` give an affine open containing the whole upper half-plane chart. `eventually_chart_mem` keeps a lift in an open containing its center. `chartEval_center` and `chartEval_at_mem` compute the actual evaluations; `chartEval_local` gives the exact valuative germ and holomorphy, and `chartEval_analyticAt` extracts holomorphy. `finitePointEval_eq` identifies the evaluations of equal points. `exists_analyticJN_ratio` expresses the second coordinate by one common ratio of sections with nonzero denominator eventually in each punctured neighborhood. |
| `Overlap.lean` | `smooth_one` gives relative dimension one; `exists_etale_affine` chooses an affine neighborhood with one étale coordinate; `etaleCoordinate_agree` gives equality of polynomial evaluations from agreement on that coordinate. `j_not_eventually_constant` rules out a locally constant j-value. `holomorphic_match` matches two nonconstant analytic germs with the same center value, with the second parameter in any specified neighborhood and away from its center. `eventually_overlap_of_complexPoint_eq` applies this to the actual normalized chart lifts of any two equal complex points. |
| `Model.lean` | `exists_stabilizer_germ_match`: from `P_N (γ₁ • τ) = P_N (γ₂ • τ)`, obtain `s : SL(2, ℤ)` fixing `τ` such that `z ↦ J_N (γ₁ • ofComplex z)` and `z ↦ J_N ((γ₂ * s) • ofComplex z)` agree as punctured germs. `complexPoint_eq_iff`: `P_N τ = P_N σ ↔ ∃ γ ∈ Γ₀(N), γ • τ = σ`. `model (N : ℕ) [NeZero N] : PreparedParam.X0Model N` adds this orbit equality to the unchanged section expansion and rational data. |
| `Specialize.lean` | `projectiveValue_eq_of_complexPoint`: over a field embedded in ℂ, if the source point becomes the chosen complex chart point and the given target point has the parametrization's complex value there, the rational evaluation equals the given target point over the field. `datumReduction_projectiveValue`: for a conductor-one datum and its source point at the datum's embedding, reducing the rational map evaluated at the source conjugate by `σ` equals `datumReduction … (conjugate dat σ)`. `hpi_iff_specialize_projectiveValue` rewrites that equality inside the actual pointwise PM comparison for every class label. `specialize_of_integral_extension`: over a separated target over the base, if two sections over the integral trait agree generically, their restrictions along the same residue point coincide; one section may be given as a source section followed by the integral parametrization. |

## Exact O.7 boundary

Fix the datum `dat := StageKummer.chosenDatum t`, let `v` be
`StageKummer.place s i`, and take its ring class field and the
restricted prime of `StageKummer.chosenDatumPlace s i t hs`. Let
`x` be the chosen source point whose image under the datum's own
complex embedding is the chart point for that datum's form. Write
`x_c = x.map (σ_c.toAlgHom.restrictScalars ℚ)`, with `σ_c` the same
`artinLabelAt … c` as in `O7Residual.At`. The fixed-scale
parametrization provides a rational `π` whose complex values are
`phiAn`. Injectivity of that embedding on elliptic points identifies
`π(x)` with `dat.y`. Naturality of projective evaluation identifies
`π(x_c)` with the Artin conjugate of `dat.y`; applying the existing
datum reduction gives the exact right side of `hπ`. There is no
new reduction map or choice of target prime.

The smallest pointwise compatibility still needed is
```text
(PMAdelic.geometricInput J G).specialize (r c)
  = datumReduction dat v (chosenDatumPlace s i t hs) (goodAt s i) (π(x_c))
```
where `π(x_c)` is evaluated as a point on the given projective
Weierstrass model. This is a specification of the missing comparison;
it is not declared as a print or a new hypothesis structure.
`StageKummer.reduceDatum` unfolds to exactly this datum reduction.
The Lean equivalence applies to `PMAdelic.geometricInput J G` without
depending on the later O.7 row constructor. The datum, form and
parametrization on the integral equation's rational fibre are taken
using the existing `EcurveZ_baseChange` identification, as in
`StageKummer.chosenDatum`.

A geometric way to supply it is the following, restricted to the points
actually used. Use the same good integral modular model, integral
Weierstrass model and restricted prime. Extend the rational `π` there.
At the reduction of each `x_c`, identify the special-fibre value of
that extension with the PM divisor-class quotient evaluated on the
based class `[r c] − [∞]`. Use the same residue embedding into
`ResidueAt v` and identify specialization of the integral
Weierstrass point with the existing `datumReduction`. The theorem
`specialize_of_integral_extension` proves the commutation on scheme
points for such a diagram by separatedness and restriction. It does
not furnish the diagram. The PM quotient and its operator relations
describe values in characteristic `p`; no field in
`PMAdelic.SpecialFibre` says that this quotient specializes the
specified rational map. For example, the operator identities are all
preserved by replacing the quotient by zero. The tree has the Néron
mapping property for a supplied smooth proper group scheme over a DVR
(`NeronExt.isNeronModelOver_of_grpObj`), which gives the usual extension
route once the compatible integral models are in place.

| Remaining input | Kind and extent |
| --- | --- |
| The chosen source point at the datum's embedding | Existing CM data and choice alignment, tex 2915–2917 and 9272–9279. Retain the source point and its embedding when choosing the datum. The characteristic-zero comparison consumes this point; it does not construct it. The analytic equality alone also does not align the reference Artin origin. |
| The labels `r c` are the reductions of those source conjugates at the detector's place | Existing Cornut–Jetchev comparison and geometric identification at the chosen reference origin, tex 9265–9279; independent of extension of `π`. An identification of the adelic orbit alone is insufficient. |
| The PM map is the specialization of the fixed rational map at those reductions, in the stage residue point type | ELLIOT, uncited standard good reduction, tex 8476–8479 (used at 9283–9291). The abstract commutative square is small. Realizing it from the current objects is substantial: the generic normalization must be identified with the generic fibre of the integral modular model, the same based rational map extended, and its specialization and residue evaluation identified with the supplied special-fibre quotient and the actual point reduction. |

## Known issues

- Tex 8468–8474: the existing source audit records that the cited
  Jetchev–Kane result omits level one. This is a citation scope error;
  the normalized-branch proof works at level one without that result.
  See `docs/research/rc-stage-kummer.md`. The primary source locator is
  **UNVERIFIED** here.
- The audit in `ZInQKernel/Contrib/OneProof/RC/PrintsAnalytic/Milne.lean`
  records that the passages cited at tex 1784 do not include the
  normalized newform statement or the Hecke identity at tex 1788; it
  also records two unused misprints in the book's modularity
  conjecture. This comparison does not invoke either claim from
  those passages.
- The base report records a possible typo in the unused Shimura 1973
  paper, p. 526 (**UNVERIFIED**): the reported coefficient expression
  is `a_n^σ f` where it should be `a_n^σ f_σ`.
- There is no counterexample to the branch statement being ported. An
  equality of two plane coordinates at just the center would not
  substitute for equality on the normalization.

## Manuscript check

| Tex lines and step | Verdict |
| --- | --- |
| 1781–1784, 1788: source locators for the normalized newform and Hecke identity. | error |
| 1785–1787, 2836–2838: rational modular curve and rational map at the fixed scale, used on interior chart points. | gap filled |
| 1825–1828: keep the period scale used by the given parametrization. | OK |
| 2915–2919: identify the interior chart at the oriented lattices, including the normalization at coincident plane values. | gap filled |
| 2915–2917: evaluate the rational map at the chosen source CM point. | OK |
| 8365–8369, 8392–8398: use the stage reduction at the detector's chosen place. | OK |
| 8468–8474: scope of the Jetchev–Kane citation at level one. | error |
| 8476–8479: good integral extension and identification with the PM special-fibre map. | unverified |
| 8480–8485: description of the reduced map as a based divisor-class quotient, used in the PM interface. | OK |
| 9265–9279: identify the coarse labels with the source reductions at the same place and reference origin. | unverified |
| 9283–9291: identify the pointwise target of specialization before scaling and summing. | gap filled |

## Verification

All five modules built with `lake --old build` targeting
`ZInQKernel.Contrib.OneProof.RC.X0Model3.Specialize` and its model
dependencies. Each Lean compiler invocation was serialized, resource
checked, and run within the 60 GB user scope. Existing dependency
artifacts were reused after source and toolchain comparison. All 35
`#print axioms` checks, including private helpers and data
definitions, report only `propext`, `Classical.choice` and
`Quot.sound`. There is no new print, axiom or admission.
