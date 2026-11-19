# RC53 coordinate comparison: unit-free reductions and the residual provenance gap


## Correction after independent review (2026-11-18)

1. **The two predicates restate the conclusion.** `RankOneCoordinateProvenanceG` and `AcyclicCoordinateConventionG` are the rank-one and acyclic restrictions of the coordinate identity (`Classification.lean`: `rankOne_is_restricted_conclusion`, `acyclic_is_restricted_conclusion`). They are casewise residual coordinate identities, not an independent provenance construction; `relIsKMG_iff_provenance_and_convention` does not reduce the open identity, which stays open.
2. **The retained-model route is too rigid at coboundary functionals.** When the functional is a nonzero coboundary `lam = β d²`, no `RetainedCoordinateModelG` exists, although the original coordinate is zero (`RetainedObstruction.lean`: `no_retained_model_of_coboundary`, with an explicit contractible example). The manuscript sets the coordinate, not every representative of the functional, to zero (tex 3889–3891, 5612–5615) and keeps homotopies in its comparisons (3837–3862, 4158–4177, 4189–4194). A homotopy-aware comparison is needed before this route can replace the coordinate link. `relIsKMG_of_retained_models` remains a sound conditional theorem.
3. **Shipped files.** The source hashes and sizes recorded further below are those of an instrumented checking edition; the shipped sources are listed here. The compiler transcripts are the `*.check.txt` files next to the sources, and there is no separate checksum file.

- `Correction.lean`: 11384 bytes, SHA-256 `fe32dadf489a102622ec751a19f61cc82f2a43b214a115069c839593e4236c48`
- `Comparison.lean`: 20844 bytes, SHA-256 `202784c3fe69f1753477facf049e8932ab6b20a864bed75a74a1cf7935f5d2c9`
- `Transport.lean`: 5758 bytes, SHA-256 `86852ed92439ec37b5c93ccce8b154c721350ed256ae86cbdb8e349628ad62c4`
- `Patterns.lean`: 7902 bytes, SHA-256 `e0d4b0b11afd7f5e60ece1c56bc8731107e96e67851b4169357b9a3c3be21d11`
- `Provenance.lean`: 6761 bytes, SHA-256 `a8d4dbbad11b9b36d261cba79206a4e44af94106d058cf18301ce0d0ad49a728`
- `Classification.lean`: 2672 bytes, SHA-256 `e412ad18b87da300acb9469b7e1ac6e56a9ea3bbd322c6689688e6c39fc6354a`
- `RetainedObstruction.lean`: 9398 bytes, SHA-256 `a01ad8aaa43e20557b4a7a745c0fdbf8cf12de62d391b36635a4f920d0d9eb0c`

The unit-free correction algebra (`Correction.lean`), the cone and adjugate comparisons, and the transport through nonzero common denominators are unaffected.

## Outcome

The fraction-field comparison does not need the premise that the correction is in the power-series group algebra with unit sign evaluations. The correction, retained-comparison, and denominator-transport reductions below are proved. The actual arithmetic relaxed-coordinate provenance is **not discharged**.

Supplied base: `6ea158a404343c90a445c129cd0d1f3a0d4b8ddc`. No existing source was edited, and no Git operations, commits, dependency updates, or target builds were performed. Verification used single-file compiler invocations after the prerequisite log reported successful completion.

The delivery contains five proof files and five compiler transcripts. Every one of the 36 theorem declarations has a signature check and an axiom check. All final compiler invocations returned exit code zero, without warnings. Every theorem's axiom list is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No new printed proposition is used. The named provenance predicates and retained-model record are explicitly **non-print** obligations. Earlier parser and elaboration attempts failed; only the final clean transcripts supplied here are claimed as verification evidence.

## What the requested interfaces mean

Let `C_x` be the sign-evaluated original complex, before new-local cancellation, and let `c_orig(x)` be its Knudsen–Mumford coordinate of the tensor formed from the given cycle and closed functional, in the retained original determinant basis.

- `RelIsKMG` asserts `u_rel(x) = c_orig(x)` whenever `Delta_x` is nonzero.
- The degenerate input of `origCoordLink_of_cases` asks for the relaxed scalar in the support-triangle record to be zero whenever `Delta_x` is nonzero and `c_orig(x) = 0`.
- Its nondegenerate input asks, whenever `Delta_x` is nonzero and `c_orig(x)` is nonzero, for an integral two-term core whose adjugate coordinate is that relaxed scalar and whose Knudsen–Mumford coordinate is exactly `c_orig(x)`.

The last theorem also assumes a power-series-group-algebra correction with unit evaluations. Those per-address inputs were not supplied as facts about the manuscript's correction. The constructors in this delivery bypass that theorem.

## Manuscript anchors

- `ex:arith-coordinate`, TeX 3877–3892: the same actual class, paired functional, complex and retained determinant basis; coordinate zero at a generically acyclic constituent.
- `ex:arith-common-coordinate`, TeX 4142–4328: the support-triangle identity (4.7), the correction factors, and `u_tilde = eta * u_rel`. TeX 4155 and 4229 expressly allow poles in the correction itself.
- TeX 4196–4224: completed-ring integrality and the factors `1 + v_q(1 + g_q)`.
- `ex:limits-fixed-field-clearing`, TeX 5509–5516: the new-local determinant factor and transport of the same class and functional.
- TeX 5605–5617: the rank-one formula and acyclic convention in the original basis.

The two target files, their coordinate dependencies, the RC53 dependency graph, and the `rc-*.md` research notes were read. No additional external-source leaf was introduced.

## Proved results

### Correction

`signEval_eta_isUnit` proves that the sign evaluation of the manuscript-shaped correction is a unit of the **completed** coefficient ring. `evK_eta_ne_zero` therefore allows its cancellation in the fraction field. Neither statement assumes a power-series-unit lift.

`poleFactor_isUnit` and `poleFactor_not_in_powerSeries` give the concrete distinction: `1 + 2/t` is a completed-ring unit, but is not the image of any power series. This is an illustrative ring example, not an assertion that a specific arithmetic prime has that correction value.

`no_completed_to_powerSeries` rules out a coefficient-compatible homomorphism from the completed ring to rational power series. A comparison of the two scalar realizations must instead use a common localization or fraction-field representative.

`relIsKMG_iff_origCoordLink` shows that, given `CorrectedIsEta`, one representation of the corrected coordinate, and fraction-field nonvanishing of the evaluated correction at the relevant addresses, the remaining obligation is exactly `RelIsKMG`. Without nonvanishing, `origCoordLink_iff_masked` gives the exact alternative: zero correction or equality of the original relaxed coordinate.

`relIsKMG_iff_origCoordLink_of_47` uses the existing ratio, inverse, support-triangle and common-coordinate hypotheses of `correctedIsEta_of_47`, and derives the needed correction nonvanishing rather than assuming it.

The quotient constructed by `relaxedFromCorrection` is representation-independent and satisfies `CorrectedIsEta` when the evaluated correction is nonzero. This pins a fraction-field value only; it does not identify that value with an arithmetic Selmer coordinate.

### Retained comparison, including zero coordinates

`exact_iff_of_exact_cone` proves that an exact comparison cone makes source and target exactness equivalent.

`kmCoord_eq_of_fourMap_total` proves the cone-coordinate formula without requiring the augmented source or target to be exact. If they are not exact, both coordinates vanish. Its retained-basis specialization is `kmCoord_eq_of_fourMap_retained_total`.

`kmCoord_twoTerm_of_adjugate` has the following mathematical statement: for a square matrix over a field with nonzero adjugate, a cycle `z`, a closed functional `w`, and `z tensor w = u * adj(D)`, the Knudsen–Mumford coordinate of the two-term complex is `u`. There is **no exact-augmentation hypothesis**. The proof constructs an exact augmentation only in the nonzero-coordinate branch; it handles zero classes and zero functionals separately.

`RetainedCoordinateModelG` records an explicit retained-comparison obligation at one address:

1. a fraction-field two-term core with a nonzero adjugate, cycle and closed functional;
2. its adjugate coordinate is the given relaxed scalar;
3. a chain map from the original complex carrying the original cycle and functional to the core;
4. the torsion of its augmented cone is the retained canonical sign.

It assumes neither a coordinate equality with the original complex nor exactness of either augmented complex.

`relIsKMG_of_retained_models` derives the requested `RelIsKMG` from these models at every nonzero-denominator address. `origCoordLink_of_retained_models` combines this with the existing `CorrectedIsEta` comparison and supplies `OrigCoordLink` with the original completed-ring correction.

**The arithmetic construction of those models remains open.**

### Nonunit-denominator transport

`isClassFunctionalCoord_transport_cleared` transports an adjugate coordinate between two injective scalar realizations of one common matrix model by clearing a nonzero denominator. That denominator need not be a unit of the common ring. The source scalar ring can itself be a fraction field.

`exists_common_coordinate_fraction` obtains such a denominator from a nonzero maximal minor. `common_coordinate_fraction_unique` proves independence of the representative. `isClassFunctionalCoord_transport_nonunit` specializes the construction to power-series coefficients and the clearing fraction field.

These theorems require a common matrix/class/functional model. They do not assert that arbitrary completed-ring elements have rational power-series realizations.

### Exact direct gap by generic patterns

Write `alpha_x` and `beta_x` for the transported free-line coefficients and `delta_i` for the three sign-evaluated Smith-block determinants. In the retained orientation,

```text
c_orig(x) = -(kappa_x * alpha_x * beta_x * delta_0 * delta_1^(-1) * delta_2)
```

`kmOrig_rankOne_formula` proves this formula from the existing determinant computation and new-local cancellation. `kmOrig_zero_iff_rankOne_tensor` proves that, at a rank-one nonzero-denominator address, degeneracy is exactly `alpha_x = 0` or `beta_x = 0`.

`relIsKMG_iff_provenance_and_convention` gives an exact equivalence:

```text
RelIsKMG
  iff RankOneCoordinateProvenanceG and AcyclicCoordinateConventionG.
```

The rank-one predicate identifies the **actual** relaxed scalar with the displayed tensor formula. The acyclic predicate gives that actual scalar the manuscript's coordinate-zero convention. Both predicates are non-print provenance obligations, with their exact TeX locators in their definitions. They have not been proved for an actual family in this delivery.

### Formal obstruction to dropping provenance

`correction_interface_provenance_obstruction` constructs constant-one scalar correction data and an empty-unused-prime support-triangle record. For any given family identification and nonzero-denominator address, the independently chosen zero cycle has original coordinate zero. Consequently both coordinate links fail for that choice, even though the correction and support-triangle interfaces hold.

This obstruction is conditional on the given identification and address. It asserts neither existence of a genuine identification nor a manuscript error, and uses no emptiness argument.

## How to integrate the proved constructors

For the direct retained-model route, supply the actual models and use:

```lean
have hrel := relIsKMG_of_retained_models M urel z lam hz hlam models
```

That result has exactly the `CoordLink.E1aG` interface and can be passed to its existing `coordLink_of_kmG`. Alternatively, combine the models with the existing correction comparison through `origCoordLink_of_retained_models`; its result is the unchanged clearing interface `OrigCoordLink`.

For the (4.7) route, use the unchanged `correctedIsEta_of_47` and the unit-free equivalence `relIsKMG_iff_origCoordLink_of_47`. This does not close the original-coordinate obligation; it isolates it.

For the pattern route, `relIsKMG_of_provenance_and_convention` supplies `RelIsKMG` once the actual rank-one tensor provenance and actual acyclic convention are established.

No use of the power-series-unit `origCoordLink_of_cases` route is necessary in any of these conversions.

## What remains open

The actual relaxed coordinate from (4.7) must be tied to the given original complex, actual retained class, the same paired functional, and the same determinant basis. An actual retained comparison model, or the equivalent rank-one provenance plus acyclic convention, would close that gap. The common-coefficient realization needed for any cross-ring scalar transport also has to come from those actual objects.

The existing records alone do not supply that dictionary; the formal obstruction above exposes the independent choices they allow. No cited printed fact was substituted for this construction.

There is **no residual need to prove a power-series-unit correction assertion** in the delivered reductions. Such an assertion is stronger than the manuscript's stated completed-ring scope and is not claimed here. The actual `RelIsKMG` and `OrigCoordLink` assertions, and therefore this arithmetic part of Theorem 5.3, remain conditional on the provenance construction.

## Source files, byte sizes and SHA-256

- `ZInQKernel/Contrib/RC53Assist/CoordLink/Correction.lean` — 12,135 bytes
  - `6eb8daebb62e11bde82f398eee272a80c4e8d92e1d76e6a64af110580c197c95`
- `ZInQKernel/Contrib/RC53Assist/CoordLink/Comparison.lean` — 21,743 bytes
  - `827e4ec50d600b16ff7e55e2c95d4381e111f1ebb57c40a229a4936054500aab`
- `ZInQKernel/Contrib/RC53Assist/CoordLink/Transport.lean` — 6,195 bytes
  - `ea7588b487e45ba96a449d1396b88514611e4b3ec5a2eafe9e54bde034e88525`
- `ZInQKernel/Contrib/RC53Assist/CoordLink/Patterns.lean` — 8,344 bytes
  - `59ec2a5dea65e125c70d890003202d255630982891cd4ae6f637a54c48c7fa9f`
- `ZInQKernel/Contrib/RC53Assist/CoordLink/Provenance.lean` — 7,259 bytes
  - `73afd81aa9d2bc76d53846984049d16d931fef8f11502facc5b2d17106bda213`

## Every theorem's exact statement and axiom output

The proof files contain all exact declarations, their context, signature checks, and axiom checks. Their final transcripts are supplied under `checks/`:

- `Correction.check.txt`: 10 theorem statements and axiom reports.
- `Comparison.check.txt`: 11 theorem statements and axiom reports, plus the retained-model record's type.
- `Transport.check.txt`: 5 theorem statements and axiom reports.
- `Patterns.check.txt`: 4 theorem statements and axiom reports, plus the explicit scalar and provenance predicate types.
- `Provenance.check.txt`: 6 theorem statements and axiom reports, plus the constant-coordinate data and support-triangle record types.

The source declarations retain explicit binder types where pretty-printing infers or elides them. The companion `SHA256SUMS` covers every source file, transcript, and this report.
