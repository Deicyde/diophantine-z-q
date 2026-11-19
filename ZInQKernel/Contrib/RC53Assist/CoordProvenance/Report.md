# Coordinate provenance: construction and residual comparison

## Result

The given class and closed functional on a genuine continuous-cochain Selmer complex can be transported to a supplied finite model without choosing unrelated vectors. The reconstructed coordinate has `RankOneCoordinateProvenanceG` and `AcyclicCoordinateConventionG`, and therefore `RelIsKMG`. Its value is independent of the retained boundary used to lift the class wherever the clearing denominator is nonzero.

**The manuscript's independently supplied relaxed scalar is not yet identified with this reconstructed coordinate.** The actual arithmetic family, its paired conjugate-orthogonal class, its common scalar realization, and its retained determinant basis still need the dictionary described below. This is a partial construction, not a completed arithmetic proof of Theorem 5.3.

Supplied integration base: `27579f4a`. Existing sources and history were left unchanged.

## Proof files

The paths below are repository-relative.

| File | Bytes | SHA-256 |
|---|---:|---|
| `ZInQKernel/Contrib/RC53Assist/CoordProvenance/GenuineRetention.lean` | 13,145 | `0396c4b5afe90485379fb57057293ad242d0b23d4d37abc90d17f397f0edbe9f` |
| `ZInQKernel/Contrib/RC53Assist/CoordProvenance/CohomologyLift.lean` | 27,512 | `e5e30f8766ff4ad1dbe5dabcfb76f982196fb03d42a0a7027ef0cef3acfe1700` |
| `ZInQKernel/Contrib/RC53Assist/CoordProvenance/RepresentativeIndependence.lean` | 10,255 | `90a3a843dc7ee83a9ed149067862d60f9c23096521aaa6bbc896d68b60132a60` |

The complete exact theorem types and individual axiom outputs are in the companion `Statements.md` and the three `*.axioms.txt` files. The source declarations retain the enclosing contexts and exact proof arguments. `Manifest.json` lists byte sizes and digests; `SHA256SUMS` covers the proof files, reports, manifest and verification transcripts.

## Genuine condition maps and the same paired functional

`GenuineRetention` constructs the primitive-to-full and paired zero-to-primitive maps on the actual continuous-cochain Selmer cones. Places are indexed by the disjoint union of old and selected places. At old places the original condition and isotropy homotopy are unchanged; at selected places the relaxed condition is the actual full local complex and the paired strict condition is zero.

Given the primitive isotropy data, `relaxedIsotropy` constructs the relaxed isotropy data. `relaxedIsotropy_retained` derives the retained-homotopy equality from these choices. No termwise tame model or independently imposed retained-homotopy equality is used.

`actual_cup_naturality` proves naturality for these actual cone maps. `actual_pairedFunctional_natural` then proves

λ_R(iw) = e λ_P(w)

for each degree-two cocycle w, from the paired strict lift jz_S = e z_P⊥ + db and its retained boundary. The primitive isotropy data and the arithmetic strict lift remain inputs; the theorem does not construct those arithmetic inputs.

The construction allows jointly continuous coefficient pairings, not only discrete coefficient modules. Its manuscript locator is ex:arith-common-coordinate, TeX 4159–4177, citing Nekovář, Sections 6.4.1–6.4.3.

## The given genuine class in the finite model

`exists_lift_with_boundary` and `lifts_differ_by_boundary` hold over any commutative coefficient ring. A quasi-isomorphism lifts a given cycle up to a boundary, and two lifts of the same class differ by a boundary in the source model.

Against `Identification2G`, `actual_class_has_model_cycle` applies this to the specified map into `galoisSelData`. `actualModelRowG` is the original-basis row of the pullback of the given integral functional L. `actualModelRowG_value` proves that every value is exactly L evaluated on the image of the original basis vector; `actualModelRowG_closed` proves integral closedness. No scalar is inserted. `same_class_and_functional_in_model` supplies the two model cochains together with their closedness and the retained class boundary.

`pairedFun_closed` supplies the closedness input when L is a traced cup functional of a supplied dual cycle. Identifying that dual cycle with the manuscript's specific conjugate-orthogonal transport is still an arithmetic obligation.

## How the two requested predicates are supplied

`actualCycleG` chooses a lift of the given genuine class with the boundary guaranteed above. `actualCoordinateG` reconstructs its coordinate, paired with `actualModelRowG`, in the original model basis: it is the explicit retained tensor formula at rank-one constituents and zero otherwise.

The following are proved without an original-coordinate-link premise:

- `actualCoordinateG_provenance`: `RankOneCoordinateProvenanceG` for this reconstructed coordinate and the reconstructed actual-data cochains.
- `actualCoordinateG_convention`: `AcyclicCoordinateConventionG` for the same coordinate.
- `relIsKMG_actualCoordinateG`: the resulting `RelIsKMG`.
- `actualCoordinateG_of_lift`: any other lift of the same genuine class gives the same original coordinate where Δ is nonzero.

This is more than independently selecting a model cycle: the cochains come from the given genuine objects, and independence of the comparison boundary is proved. It is nevertheless not an identification of the scalar previously supplied by the manuscript's correction construction.

For that supplied scalar, the exact remaining input is

```lean
∀ x, evK (sgnChar x) M.toIdentification.B.Δ ≠ 0 →
  urel x = actualCoordinateG M zSel hzSel L x
```

`provenance_of_actual_dictionary` converts this input into both requested predicates and `RelIsKMG`. `origCoordLink_of_actual_dictionary` combines it with the unchanged `CorrectedIsEta` interface and supplies `OrigCoordLink` with the original completed-ring correction.

`origCoordLink_iff_actual_dictionary` proves the reverse equivalence when one corrected-coordinate representation is supplied and the original correction is nonzero in the fraction field at the relevant addresses. The existing unit-free (4.7) correction route supplies these correction facts. No premise that the correction is a power-series unit is used.

## Retained comparison on cohomology, including zero coordinates

`RepresentativeIndependence` constructs the two elementary graded shears for a class boundary and a dual functional boundary. Their determinants are one. `kmCoord_class_boundary` and `kmCoord_functional_boundary` consequently prove representative-independence for every four-term complex over a field, with no exact-augmentation hypothesis.

`kmCoord_retained_cohomology_comparison` extends the retained comparison to maps carrying the same class and functional only up to retained boundaries. It requires the actual comparison map and its retained cone-basis identity, but neither exactness of the augmented source/target nor nonzero class/functional. It applies at zero coordinates and acyclic constituents as well.

## What remains open precisely

1. Construct the manuscript's actual arithmetic coefficient family and retained bounded model, with the specified class and conjugate-orthogonal paired functional. The present `Identification2G` results are conditional on that given model and the genuine cochain data.
2. Construct the common coefficient and retained determinant-basis comparison proving the displayed scalar dictionary for the actual (4.7) relaxed scalar. A bare quasi-isomorphism, correction identity, or support-triangle scalar record does not supply this comparison.
3. Keep the graded model correct. The manuscript's full-condition singular blocks are in degrees one and two, so their retained determinant factor is `det(B)⁻¹`. The supplied `Identification2G` coordinate interface instead uses degree-two-to-three blocks and `det(B)`. The new reconstruction is stated for the supplied interface; it does not convert the full-condition `Identification3` model into it. Use the correct full-condition interface, or construct an actual graded retained comparison. No empty-place or zero-coefficient substitute was used to assert this identification.

`Scope.md` records the mathematical details and locators. No additional printed proposition is introduced, and the residual dictionary is explicitly not a printed leaf.

## Verification

All three final proof files compiled as single files after the prerequisite build reported successful completion. Their final compilations and all three complete theorem audits returned exit code zero with no warnings. There are 37 theorem declarations: 5 in `GenuineRetention`, 23 in `CohomologyLift`, and 9 in `RepresentativeIndependence`.

Every theorem's individual axiom output is exactly

```text
[propext, Classical.choice.{u}, Quot.sound.{u}]
```

The only axioms are the standard three. Final proof files contain no proof placeholders or diagnostic commands, and their heartbeat bound is 800000. No existing file edits, history operations, commits, dependency updates, package builds, auxiliary agents or external messages were performed.
