# Central finite-stage boundary: corrected scope and stronger conditional contract

## Verdict

The coefficient quotient, actual finite Kummer projections, continuous local `honto`/`hinj` proofs, and canonical comparison of closed cochains with first cohomology are valid partial results. **All their mathematical declarations are unchanged.**

`CentralRetainedInput` is an **unrestricted conditional packet**, not an identification of the actual retained finite model or arithmetic stage. Its projections, matrix, coordinates, place partition and global representative are free inputs. `centralRetainedStage` preserves those supplied inputs and proves a conditional coordinate boundary, but this does not realize the manuscript's finite Heegner construction. The earlier interpretation of the record as intrinsically identified arithmetic/model inputs is withdrawn.

These obstructions were found in an independent review. They are statements about what the interface certifies, not failures of the kernel or counterexamples to the conditional boundary theorem.

The new `PinnedConstruction.lean` enforces stronger **conditional object-level bindings**. It takes a named source cycle independently of the packet, computes the norm stage from specified geometric data, requires the old Kummer partition to contain the fixed places above `2N`, and obtains both model projections from a full specified deformation retract. This rules out erasing the projections while keeping the same nonzero model and comparison. It does **not** construct or identify the actual finite Heegner source or actual normalized model from arithmetic.

`BaseZeroLeafInputsText` and Theorem 5.3 remain open.

## Source files

All files are in `ZInQKernel/Contrib/RC53Assist/Boundary45Stage/`.

- `Identification.lean`: 76,703 bytes; SHA-256 `4245158c7bcac60a305cde6dfa003148a9ef74109a433f0a832ab6c432c899a6`. This edition corrects scope docstrings only. Its 68 theorems and every other mathematical declaration are unchanged.
- `Obstructions.lean`: 11,099 bytes; SHA-256 `236600bf14cc19b8a20ef815522c809f4db5f620c58be5f5da8857a31838c014`. Nine theorems and two definitions record the independent-review obstructions.
- `PinnedConstruction.lean`: 22,916 bytes; SHA-256 `07aef9b96ba24dd0570d63d74802f3b6a488826516867734e69f3b3c0a6c1878`. Twenty-two theorems and seventeen other named declarations give the stronger conditional contract and its safeguards.

`COMMENT_ONLY.diff` lists every change to the original source. Removing comments and normalizing whitespace produces exactly the same mathematical source before and after the correction. The original source/report are preserved in the original packet; `REPORT.initial.md` preserves the original report byte-for-byte. The original manifest and theorem receipts apply to that earlier packet, not to the corrected documentation edition.

## Accepted partial results

- The actual central coefficient module is identified additively with `M/tM`; coefficient semilinearity and Galois compatibility are proved separately.
- At the base, the actual finite coefficient character evaluates to one at `t = 0`.
- The actual twist, torsion and decomposition coefficient maps and Kummer cochain spans project to the specified central maps and spans.
- `centralSelData_localHypotheses` proves the exact two representative-level local hypotheses on the displayed continuous datum.
- The ambient quotient `C^1/B^1` does not weaken equality of closed representatives: its comparison with actual first cohomology is injective with the correct representative formula.
- `centralRetainedStage` sets `S := T` and fixes the ambient cochain groups/maps to the displayed datum. This is preservation of a supplied stage, not identification of it with the actual ring-class/CM stage.

The quotient equivalence is additive; its semilinearity and Galois formulas are separate proofs. It is not a derived base-change comparison of entire Selmer complexes.

## Recorded obstructions

The namespace is `ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Obstructions`.

### A1: the model can be erased

`eraseModel` takes any conditional packet and replaces its model fields by

```text
p1 = 0, p0 = 0, dC = the supplied matrix, zeta = 0, jay = 0.
```

`eraseModel_spec` proves that the original global/local representatives and fixed place partition are untouched. The construction works with any coefficient-support inclusion, not only equal supports.

### A2: the class premise is the global boundary obligation

`class_premise_iff_global_boundary` proves, for the genuine central datum `D` and every first cochain `zG`,

```text
cochainClass D zG = globalKummerMap(L • T.W)
  iff
exists g, dG0 g = zG - L * (T.a - 2) • globalKummerCocycle(P).
```

The packet's `hzcls` field therefore does not derive that obligation for the finite Heegner representative already specified by the manuscript.

`zeroProjectionInputFixed` manufactures representatives by scaled copies of a single Kummer Selmer lift of `P`. It accepts a fixed old-place partition and any supplied model matrix. `zeroProjectionInputFixed_spec` records its exact multiplied Kummer representative and zero projection.

### A3: the empty partition gives an all-full example

`emptyPartition_at`, `emptyPartition_conditions` and `emptyPartition_data` prove that `Pold = ∅` and coefficient support equal to Selmer support make every condition full. `fullPattern_lift` then provides a Selmer lift of every closed global cocycle.

`arbitrary_model_record` accepts any matrix and ranks, using only the original actual torsion/division inputs and a supplied norm stage. `positive_precision_trivial_stage` specializes this to

```text
i = 1, L = 1, N = M0 = 1, dC = identity,
p1 = p0 = zeta = jay = 0, S = selfStage P.
```

No moving prime, ring-class field or CM point is required by this unrestricted packet. These examples remain valid; the accepted conditional algebra was not changed to invalidate them.

## The stronger conditional contract

The namespace is `ZInQ.Manuscript.RC.BaseZeroAssembly.Boundary45Stage.Pinned`.

### The source is a separate specified input

`SpecifiedHeegnerCycle D` is the named global/local cone representative supplied by the construction, with its closedness and cone equation. The wrapper takes a **fixed `Z : SpecifiedHeegnerCycle D` before forming a packet**. It never chooses `Z` by an existential packet construction.

`SpecifiedFiniteHeegner … Z` has no field that can choose a replacement Heegner global/local representative. It carries the specified geometric stage data, place requirements and a lift of the actual Kummer cocycle. `ConstructedClassIdentity … Z A L` is the explicit remaining class-identity premise for that same fixed source.

The class premise remains mathematically equivalent to the global-boundary obligation for that fixed source. Naming and pinning the source does not prove this arithmetic equality. `pinnedRetainedStage_source_not_replaced` proves that a distinct fixed source cannot be replaced by the multiplied Kummer cocycle used in the adversarial construction.

### The stage is computed from specified geometric data

`SpecifiedNormGeometry` contains a specified finite normal extension inside the support field, its actual automorphism and point groups, a subgroup/transversal, specified point candidates, Frobenius, trace, split norm equality and point-trace identity.

`SpecifiedNormGeometry.stage` computes `geometricSplitNormStage` from those objects; there is no independent `SplitNormStage` field to replace. `stage_spec` records the actual point/Galois groups, inclusion, moving point and trace.

This still does **not** certify that the specified extension is the ring-class field, that the point candidates are the manuscript's CM points, or that the marked moving place is the prime of this conductor extension. Those arithmetic interpretations remain external obligations. A named arbitrary extension with a norm equality cannot be called an actual ring-class construction on the strength of this record alone.

### Fixed places above 2N must be Kummer places

`fixedPlacesAboveTwoN N` is the actual ideal-membership set of primes above the specified integer `2N`. `FixedPlacesIncluded` requires it to be contained in `Pold`.

The construction parameter additionally supplies an actual dyadic place and its ideal-membership proof, requires `Pold ⊆ S0`, and marks a full moving place in `S0`. `specifiedConstruction_partition_not_empty` rules out the empty partition. `specifiedConstruction_moving_not_fixed` proves that the marked moving place is not one of the fixed places above `2N`.

The identification of the integer `N` with the curve's conductor, and of this partition/support with the actual construction, is not produced by these ideal-membership facts.

### Every model projection comes from one fixed deformation retract

`FiniteFreeModel i` is a specified complex over the actual ring `Z_2/(2^i)`, with a finite-rank basis in every degree, bounded rank support and a specified lift of its degree-zero differential. Its coordinate differential equation is tied to that same basis.

`ModelComparison D M` carries explicit chain maps `projection`, `sectionMap` and an explicit degree-minus-one `homotopy`. `DeformationRetractContract` requires, in **every** degree,

```text
projection ∘ sectionMap = identity on the model,
d h + h d = identity - sectionMap ∘ projection,
h ∘ sectionMap = 0, projection ∘ h = 0, h ∘ h = 0.
```

The maps are linear for the canonical integral action on the underlying additive complexes. No further coefficient-linear or derived arithmetic comparison between the different coefficient-ring presentations is inferred from this contract.

`modelProjection0` and `modelProjection1` are **defined** from the same comparison and bases. They are not fields of a freely chosen packet. `modelProjection_d` derives the consumer's degree-zero square from the full chain comparison. `PinnedCoordinates` ties the specified integral coordinate lifts to the projection of the fixed source and fixed Kummer lift.

`retract_projection_surjective`, `modelProjection1_surjective` and `modelProjection0_surjective` prove that these projections are onto their specified model terms. `coordinateRing_one_ne_zero` proves that the finite coordinate ring is nonzero at every positive precision.

`pinnedRetainedStage_projections_not_zero` then proves that at positive precision and positive degree-zero/degree-one ranks, **neither** projection can be zero. Thus the `eraseModel` operation cannot preserve the same pinned nonzero model and deformation-retract contract. It is not claimed that an actual model comparison has already been constructed.

### The conditional consumer and finite boundary

`pinnedPacket` supplies the unrestricted packet only after the source, geometry, place requirements, full model comparison and coordinates have been fixed. `pinnedRetainedStage` is its exact `RetainedStage45` consumer. `pinnedRetainedStage_spec` proves preservation of the fixed source, computed geometric stage, projections, model differential and coordinates.

`pinnedRetainedStage_exists_witness` proves

```text
exists v, for every coordinate a,
  zeta(a) - L * (specified trace - 2) * jay(a) - (model differential v)(a)
  belongs to (2^i) in Z_2.
```

Its premises retain `ConstructedClassIdentity` for the fixed source, the specified construction object, the specified finite model/deformation retract, and their coordinate-lift identities. It is not an unconditional arithmetic boundary theorem.

## Remaining arithmetic obligations

1. Identify the named source cycle `Z` with the actual finite Heegner construction, and prove its `ConstructedClassIdentity` from the actual construction, transfer and Kummer comparisons. The new wrapper does not eliminate this conclusion-equivalent global premise.
2. Construct the actual ring-class fields, CM points, moving prime, Frobenius, subgroup/transversal and trace identity, or provide verified comparisons to the fixed geometric inputs. The marked moving place is not yet linked to the extension's conductor.
3. Identify the curve's conductor integer, actual support and old Kummer partition with the pinned place data.
4. Prove `GlobalDivisionPointsInSupport` for those supports. It is not a consequence of `FullTorsion` supplied here.
5. Construct the actual local Selmer-cone representatives and their compatibility.
6. Construct the actual finite free model and its normalized deformation retract, including compatibility of the full original local/Selmer complexes with the central datum under coefficient/support change. The contract is not an existence proof for that comparison.
7. Supply the actual stage family, uniform bounds and unchanged limit comparisons of `InnerLimit45Base.ofStages`, and tie its output to the specified specialized cycle and conductor-one point.

Changing the named construction or model inputs can still change the mathematics. The stronger wrapper blocks the demonstrated shortcuts **for fixed inputs**; it does not replace their actual arithmetic realization by a label or an arbitrary record.

## Verification and edition discipline

`THEOREMS.review.md` and `THEOREMS.review.json` give the exact new statements and individual kernel dependencies. The corrected original source is freshly checked as well. `MANIFEST.review.json` records the source and receipt hashes, compilation exits, axiom union and comment-only equality check.

The permitted single-file checker, six threads, CPU affinity 16–31 and niceness 10 were used. All three final production checks exited 0 with no diagnostics. Fresh source-copy audits checked 166 named declarations, including all 31 new theorems; every dependency report contains only `propext`, `Classical.choice` and `Quot.sound`. These reports do not discharge the explicit arithmetic and model-comparison premises.

No existing mathematical declaration, dependency pin or unrelated file was changed; no version-control operation, repository build, checkout, commit or human message was performed.

The earlier source/report and proof history are retained in the original packet and original receipts. Only the specified scope docstrings and current report were corrected. Scratch checking directives are not present in any production source.
