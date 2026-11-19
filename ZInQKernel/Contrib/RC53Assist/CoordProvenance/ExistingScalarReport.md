# Existing relaxed scalar and retained graded coordinates

## Status

This is a verified partial construction, not an instantiation of the arithmetic coordinate identity for Theorem 5.3. The existing relaxation scalar is extracted from its existing adjugate identity and transported without redefining it. Homotopy-aware comparison then identifies its coordinate in the original determinant basis, up to the computed retained factor. A common corrected representative and a retained cone basis give the unchanged `RelIsKMG` and `OrigCoordLink` consumers.

The concrete common field `Frac Λ`, its two injective realizations, the finite coefficient/sign/matrix/vector/pre-complex diagrams and the corrected fractional representative are now constructed. What remains is to identify the stored endpoint matrices and representatives through those realizations with the same actual Selmer class and paired functional, realize the actual correction, and compute the retained cone basis. The integral `Identification3` to `Identification2G` adapter has not been constructed. The localized inverse-disk adapter proved here is a coordinate-level adapter of graded finite shapes, not a cast of those identification records.

## Mathematical locators

The relevant passages of `diophantine_zq.tex` are:

- TeX 3837–3862: class and functional representatives, with their retained homotopies;
- TeX 3877–3892: the determinant coordinate and its zero convention;
- TeX 4142–4240: the actual relaxation diagrams and the existing scalar in (4.7);
- TeX 5481–5730: determinant factors, retained finite models and denominator clearing.

No new printed proposition is introduced. All new results are algebraic consequences of their displayed cochain, matrix, coefficient and basis data. No power-series-unit lift of the completed-ring correction is assumed.

## Source organization

The four source files are `ExistingScalar.lean`, `EndpointComparison.lean`, `FullModelAdapter.lean` and `CoefficientRealization.lean`.

`ExistingScalar.lean` uses namespace `ZInQ.Contrib.RC53Assist.CoordProvenance.Scalar`.

The new comparison conclusions use namespace `ZInQ.Contrib.RC53Assist.CoordProvenance.Endpoint`, with the unchanged clearing consumers in its `Clearing` namespace. The earlier homotopy comparison is reproduced in `EndpointSupport`, and the common-fraction lemmas are reproduced in `EndpointScalarSupport`. These separate namespaces make the file self-contained and avoid redefining declarations of the earlier delivered edition. They are not changes to that edition.

The full-condition finite shape and its cancellation proofs are reproduced in `FullConditionSupport`. The new adapters use its `Adapter` namespace. This is the same graded matrix shape as the full-condition construction, in a separate namespace; it is not a nominal conversion from the original `Identification3` record. The full cancellation definition is reducible in this copy, and two existing cancellation proof endings are simplified accordingly. The mathematical differentials, class and functional formulas are unchanged.

`CoefficientRealization.lean` uses namespace `ZInQ.Contrib.RC53Assist.CoordProvenance.Coefficients`. Its common field and coefficient maps are concrete, not parameters awaiting a completion-map assumption.

The exact elaborated statements of every explicit declaration, together with its individual axiom report, are supplied in `ExistingScalarStatements.md` and the four `.axioms.txt` files. The manifest distinguishes the 50 new theorems from the reproduced support theorems.

## 1. The already existing scalar

`existing_relaxation_endpoint` applies the last actual relaxation step to the support with one unused prime removed, and rewrites its endpoint by `T.hrel`. It obtains

`IsCoordOn D z w T.urel`.

Here `T.urel` is the existing field of `CommonCoordinateTrianglesN`. No new scalar is defined as a substitute. The extracted matrix and vectors are those supplied by the step, not independently chosen matrices.

`existing_endpoint_on_carrier` gives the same extraction for an arbitrary commutative scalar carrier. It can therefore be used with a Laurent carrier without requiring the relaxed scalar to lie in rational power series.

`existing_scalar_no_unused` handles the empty support separately: the existing relaxed scalar is the existing primitive scalar. It does not manufacture a last step when none exists.

`isCoordOn_relabel` and `existing_relaxation_endpoint_finite` relabel the same matrix and vectors by a positive finite index `Fin (m + 1)`, preserving the scalar exactly.

`toLaurent` is the actual inclusion of rational 2-adic power series into rational 2-adic Laurent series. `toLaurent_injective`, `isCoordOn_map` and `existing_relaxation_endpoint_laurent` transport the same endpoint through this inclusion. This inclusion is not a homomorphism from the completed coefficient ring into Laurent series. The generic carrier theorem and the clearing consumers allow a supplied Laurent scalar that is not the image of a power series.

## 2. A common numerator and a possibly nonunit denominator

Suppose the endpoint matrix, class and functional are realized over a common commutative ring `R`, with injective maps

`f : R →+* A` and `g : R →+* K`,

where `K` is a field and `A` may be the Laurent carrier. If the existing scalar `u` satisfies the endpoint adjugate identity in `A`, and `D.adjugate` is nonzero, `existing_scalar_common_fraction` constructs `num` and `den` in `R` with

`den ≠ 0`, `f den * u = f num`,

and the same adjugate identity over `K` for `g num / g den`.

The denominator is an actual nonzero entry of the adjugate. It is not assumed to be a unit in `R`. The numerator is the product of the corresponding class and functional entries. The full matrix identity is reflected through the injective map, so the chosen entry fixes all other entries, not just one ratio.

`existing_scalar_unique` proves uniqueness for the same realized matrix and vectors.

`existing_scalar_from_corrected_representative` reflects a shared cleared correction identity into `K`. It cancels only nonzero evaluated denominators and the nonzero evaluated correction. It identifies the supplied existing relaxed scalar in `K` with `g num / g den`; it does not require a correction unit in the power-series ring.

`existing_laurent_scalar_common_fraction` specializes the two carriers to rational 2-adic Laurent series and the fraction field of the completed coefficient ring.

The hypotheses here must come from actual common coefficient data before the two completions/realizations. Choosing `R` to be the whole completed ring and inventing a coefficient homomorphism into Laurent series is not justified by these results.

## 2A. Concrete coefficient and local-matrix diagrams

`CoefficientRealization.lean` constructs `CommonField = Frac Λ` before either completion/realization. Its actual integral maps are the coefficientwise inclusion `ιQ` followed by the power-series-to-Laurent inclusion, and `ψO : Λ → Frac 𝒪`. The injection of `Λ` into `𝒪` is the existing proved `lamToO_injective`. The universal property of the fraction field gives `toLaurent` and `toClearing`, both proved injective. Neither construction maps the entire completed ring to Laurent series.

`signToCommon`, `sign_toClearing` and `sign_toLaurent` give the actual sign-evaluation square for the integral family coefficient algebra. `matrix_toClearing`, `matrix_toLaurent`, `vector_toClearing` and `vector_toLaurent` prove it for every rectangular matrix and every integral class/functional vector. Thus these diagrams apply to the finite integral local, orthogonal and conjugation matrices once those matrices and representatives are supplied; they do not assume the desired coordinate equality.

`commonPre_toClearing` realizes the supplied integral pre-complex degreewise as exactly `PreComplex'.toFour ((C.map (φO b)).map (evK χ))`. `commonPre_toLaurent` realizes the same integral differentials in the Laurent carrier. These are actual finite coefficient diagrams, not a coefficient-change functor for genuine continuous cochains.

`local_block_regular_common` derives nonzero determinant of every common-field sign-evaluated local block from its actual invertibility after coefficient change to `𝒪[G]`. It does not assume invertibility in `Λ[G]`. `inverse_toClearing`, `inverse_toLaurent`, `schur_toClearing` and `schur_toLaurent` then transport the same inverse and local cancellation differential to both fields.

`correctedCommon e a = ofIntegral a / 2^e` is the common expression for the already supplied corrected representative. `corrected_toClearing` proves its clearing image is exactly the existing `uK e a`. `corrected_toLaurent_fraction` and `corrected_toLaurent_rep` prove its Laurent image is the existing corrected power-series representative `C((2^e)⁻¹) * ιQ a` under the actual inclusion. This identifies the corrected representative, not a replacement definition of the relaxed scalar.

The source uses fully qualified determinant sign evaluation to avoid ambiguity when the four self-contained bodies share a scope. The corrected standalone types are unchanged from their earlier standalone probe; that correction concerns source compatibility, not a change to the mathematical coordinate convention.

## 3. Same actual class, paired functional and original basis

`endpoint_row_of_values` identifies the supplied endpoint row with the row of the actual functional on the actual target finite model, from its values on that model.

`existing_endpoint_original_basis` takes two finite-model maps into the same cochain complex, both quasi-isomorphisms; the already supplied endpoint cycle and source cycle lifting the same actual class up to displayed boundaries; and the endpoint row giving the values of the same actual closed functional. It constructs the comparison map and both homotopies. No coordinate equality is an input to this construction.

The functional homotopy is retained in the degree-three augmented map. In particular, a nonzero coboundary functional is not forced to be the zero cochain. The total cone-coordinate comparison is applicable at zero-coordinate cases as well as nonzero-coordinate cases.

For the existing endpoint scalar `u`, the result is

`kmCoord(source, original basis) = retainedFactor * u`.

The retained factor is the source parity sign divided by the augmented comparison cone torsion. It is proved nonzero from the quasi-isomorphism. It is not thereby proved to equal one or to be an integral unit.

`existing_endpoint_two_realizations` combines this constructed comparison with the common numerator and denominator. Its output is an original-basis coordinate of the same actual class and functional, equal to the computed retained factor times the transported existing scalar.

`original_coordinate_eq_existing_relaxed` combines the existing endpoint identity, a shared corrected representative, a homotopy-aware comparison, and the retained cone basis equation. It proves the original coordinate equals the existing relaxed scalar in the clearing field. The retained basis equation is a determinant-basis condition; it is not inferred from mere cone exactness.

For genuine Selmer data, the reproduced comparison machinery constructs the functional from the manuscript pairing order `PD(-, conjugate class)`. Its cochain closure, representative homotopies and finite-model comparison are the earlier proved algebraic constructions. This continuation has not supplied the arithmetic finite-model maps for the stored endpoint matrices.

## 4. Unchanged clearing consumers

`ExistingRelaxationRealizationG` records the common ring, its two actual coefficient maps, the existing Laurent endpoint adjugate identity, the corrected numerator and denominator, the same class/functional comparison, and its retained basis. Its Laurent scalar is a parameter: the existing scalar supplied by the caller, not a scalar defined by this record.

`relIsKMG_of_existing_realizations` consumes these realizations at the regular addresses together with the existing corrected representation and nonzero evaluated correction. It proves the unchanged `RelIsKMG` conclusion.

`origCoordLink_of_existing_realizations` then proves the unchanged `OrigCoordLink` conclusion.

These are sufficient-data consumers, not a construction of their `models` input. Merely defining this record, or supplying an existence hypothesis for it, does not close the arithmetic identification. The endpoint part must be obtained from the actual stored relaxation step after identifying its common coefficient model; the class/functional comparison and retained basis must be obtained from the actual local/coefficient diagrams. Neither `RankOneCoordinateProvenanceG` nor `AcyclicCoordinateConventionG` is used as an input or counted as independent provenance.

## 5. Correct grading and the inverse-disk adapter

The full-condition complex has a singular local disk in degrees one and two. Cancelling its invertible block `B` leaves

`d0 = c0`, `d1 = P - Q * B⁻¹ * T`, `d2 = U`,

and its original determinant coordinate is `det(B)⁻¹` times the remaining coordinate.

The legacy pre-complex puts its local disk in degrees two and three, where cancellation contributes `det(B)` rather than its inverse. A same-block degree shift is therefore not a harmless relabeling of a retained determinant basis.

`inverseDiskLegacy` adjoins the inverse disk `B⁻¹` in the legacy position over a field. Its remaining complex is exactly the full-condition remaining complex, as proved by `inverseDiskLegacy_cancel`.

`fullToLegacy` is an explicit chain map. Its degree-one component projects the original full cycle to its unchanged remaining component. Its degree-two component uses the actual Schur projection. `fullToLegacy_class` and `fullToLegacy_functional` prove that it transports the same class and the same closed functional, not rescaled substitutes. The functional on the added inverse disk is zero, while the actual remaining functional can be a nonzero coboundary.

`legacy_cycle_closed` and `legacyFunctional_closed` prove closure of these transported representatives.

`full_coordinate_eq_inverseDiskLegacy` proves equality of the original retained coordinates of the two graded shapes. The equality is total, including zero coordinates. Its determinant calculation is

`det(B⁻¹) = det(B)⁻¹`.

`same_disk_factor_obstruction` proves that a same-block degree shift cannot preserve a nonzero coordinate factor when `det(B)^2 ≠ 1`.

`inverse_matrix_lift_forces_integral_unit` proves that an integral, coefficient-compatible lift of the inverse matrix forces the original determinant to be a unit already in the integral ring. `no_integral_inverse_disk_lift` rules out such a lift when that determinant is an integral nonunit, even if it becomes a unit after coefficient change.

Consequently, the localized inverse-disk adapter is not automatically a truthful integral `Identification2G` record retaining the same Frobenius blocks and actual local diagrams. Inverting a block can also change its arithmetic interpretation; integral invertibility alone does not supply all the identification-record fields.

## Exact remaining arithmetic obligations

1. **Match the actual data in the common realization.** The common field `Frac Λ` and both injective coefficient maps are constructed, with diagrams for all finite integral matrices and vectors. Identify the stored endpoint matrix, actual class vector, actual paired row and actual correction in that field (or a verified bounded common subring where needed). Verify `eta_realization` and the Laurent corrected-product identity for the existing relaxed scalar. The existing corrected representative itself now has proved images in both fields. No completed-ring-to-Laurent map is supplied.
2. **Stored endpoint finite model.** Identify the matrices and vectors extracted from the actual relaxation steps with finite models of the manuscript's actual relaxed/full Selmer complex. Construct the model maps through the same actual cochain complex, using the orthogonal, conjugation and retained local isotropy data. Prove the displayed class boundary and functional-value identities. The existing abstract `ActualStep` alone does not provide these model maps.
3. **Regularity of the target core.** Prove the extracted target adjugate is nonzero at the regular addresses, from the actual finite-model rank information. `local_block_regular_common` supplies local-block regularity, not the nonzero adjugate of the separately stored target core. This does not require the scalar or functional class to be nonzero, and must not discard the acyclic case.
4. **Actual retained basis.** Compute the augmented comparison cone determinant in the manuscript's retained graded bases. Prove the parity-normalized cone torsion is the required retained factor, or equal to the parity sign for the unchanged clearing consumer. The nonzero torsion theorem alone is insufficient.
5. **Identification-record bridge.** Use the correctly graded full-condition finite model. Either prove all fields of a genuinely coefficient-compatible integral adapter, including the unchanged local arithmetic interpretation, or supply the downstream coordinate/clearing consumer for the actual `Identification3` full-grade model directly. The proved inverse-disk adapter supplies the field-level coordinate calculation and an integral-lift obstruction, not that record bridge.

Thus the actual (4.7) scalar has not been replaced, and the final missing work is concrete arithmetic/model/basis data rather than a casewise coordinate-identity hypothesis. The new consumers are ready to use once those data are constructed.

## Evidence

There are 50 new theorems: 12 scalar theorems, 6 endpoint/clearing theorems, 10 graded-adapter theorems and 22 concrete coefficient-diagram theorems. Every new theorem's individual axiom list is exactly `propext`, `Classical.choice`, `Quot.sound`.

All 201 explicit declarations, including all 132 theorem declarations in the four self-contained files, are audited individually. Their axiom lists contain only subsets of those three standard axioms. The reproduced `FullPreComplex.zeroGCx_acyclic` theorem uses `propext` and `Quot.sound`, without `Classical.choice`.

Each of the four final source files compiles with no diagnostics under the prescribed single-file command, six threads, CPU affinity and heartbeat limit. A combined-source check of all four files also compiles with no diagnostics, verifying that their namespaces and coefficient diagrams coexist. `CompileReceipt.json` records the successful exits and hashes of the unchanged empty compiler logs; empty files cannot be included in the published bundle.

The four `.axioms.txt` files give readable types and per-declaration axiom reports. The four `.exact.txt.gz` files preserve the fully explicit kernel-type renderings byte-for-byte; decompress them to the corresponding `.exact.txt` files before using the byte/line ranges in `ExistingScalarStatements.md`. These exact renderings include existential binder types, universes and proof arguments, with no printer ellipses. The temporary audit and combined-source files are not part of the delivery.

The final manifest records source sizes and SHA-256 values, compiler outcomes, declaration counts, individual axiom reports and the simultaneous namespace-compatibility check. Earlier delivered source/report editions are checked against both of their existing checksum lists and left unchanged.
