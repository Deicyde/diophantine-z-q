# Moving derivative labels and retained consumers

## Construction order

A derivative label is a sequence of actual arithmetic primes, not a fixed characteristic-zero place. The coefficient stages share one precision system and one nonprincipal ultrafilter. Lift the finite matrices and all diagram maps over the integral coefficient ring, take their matrix limits, and only then localize at a selected height-one prime and pass to its residue field.

`MovingDerivativeLabel` records natural prime values, quadratic and imaginary-field data, avoidance, rational arithmetic Frobenius elements, primes above them, degree-two residue sizes, local arithmetic Frobenius lifts, the actual twisted coefficient action, the Tate comparison, the character precision, and a common precision sequence. Its coefficient-action congruence is proved from the character and Tate comparisons; it is not inferred from Tate congruence alone.

The arithmetic consumer also accepts `RealizedLabel` from the arithmetic realization contribution. Its entry conditions retain quadratic degree, nontrivial conjugation, actual degree-two residue cardinalities, and inclusion of earlier selected primes in the excluded finite sets. These are arithmetic inputs, not existence theorems supplied by this contribution.

## Cochain comparisons

The matrix Selmer differential is the actual cone block differential on global, condition, and shifted-local coordinates. Its square follows from the retained differential and map identities. The scalar-limit comparison is a cochain isomorphism induced by those coordinate maps.

The four local conditions have coordinate ranks zero, two, two, and four in degree one, while all retain the degree-zero Tate term. The finite and singular inclusions are the first and second coordinate halves. The comparison preserves those inclusions.

For a fixed finite label set, concatenate the actual coordinate modules by a disjoint-union index. Condition inclusions are block diagonal and the retained localization is the tuple of the label maps. `labelMatrixSideIso` identifies the whole configured Selmer complex with the limiting matrix cone by an actual cochain isomorphism.

`movingFiniteSide_Dside` and `movingSingularSide_Dside` identify the side data with the selected configuration and its insertion as Selmer data, not merely by dimension. `movingSides_Dstr` proves equality of the strict data. The associated stage equivalences are derived through `labelMatrixSideIso`, canonical scalar-extension coordinates, and a computed based minimal model.

## Stage models and actual classes

`IntegralMatrixStageData` specifies residual two-term shape, an integral class and functional, and the generic determinant/adjugate conditions of the computed model. `canonicalMatrixModel` is obtained by unit-disk cancellation of the specified bounded finite-free complex. No side cohomology equivalence is an input.

`BasedTwoTermModel.stage_class` retains the specified actual class up to its explicit boundary witness. `BasedTwoTermModel.stage_functional` retains the pullback of its functional. The actual class is never replaced by a primitive kernel vector.

The residual comparison uses scalar extension of the retained homotopy equivalence. It does not assume flatness and does not interchange cohomology with the limit.

## Connecting maps

`iteratedSelmerIso` preserves all old conditions. Its quotient-map square and `iteratedLocalization_natural` preserve localization.

The strict/relaxed matrix-coordinate sequence is transported from the actual limiting change-of-condition sequence through the derived cochain isomorphisms. Its short exactness is proved. `matrixStrictSequence_delta` identifies its genuine connecting map with the limiting connecting map, including the sign convention.

## Local pairing transfer

`RetainedScalarUnit` retains a value and its inverse modulo each stage ideal. This proves that its integral limit is a unit and every fixed-prime specialization is nonzero. Stagewise nonzero scalar values alone are not used.

The cross and residue coefficient matrices are explicit polynomial matrices. Their integral limits and coefficient changes are proved to commute with the same formulas. `RetainedLocalCupStages` records the finite-stage degree-one residue comparison and the degree-two/degree-zero comparison, together with retained scalar inverses. From these finite-stage inputs, the degree-one identity and top-degree perfectness required by the retained duality certificate are proved.

`integralConjMatrix` is the matrix of the actual conjugation in the retained Tate basis. Its specialization is exactly `conjMatrix`. `RetainedTateFrame` retains an invertible integral coordinate change and its conjugation intertwining identity. The actual rational Frobenius matrices in that frame tend to the same integral conjugation matrix. The resulting pairing certificate therefore uses the required actual `conjMatrix`, not a free involution. `RetainedTateFrame.orientation` and `RetainedTateFrame.fibre_orientation` preserve the arithmetic determinant minus one through the same integral coordinate change and fixed-prime specialization.

## Conditional consumer

`retainedRestrictionStages` is derived from the restriction matrices of `RetainedLimitPairingStages`. `retainedRestriction_eq` proves that its limiting cochain map is exactly the restriction used by the retained duality certificate.

`fibreFiniteStageEquiv` and `fibreSingularStageEquiv` supply the two side-to-stage equivalences from their integral matrix data. `derivedFibreNonquadStep` passes them to the existing conditional consumer. `retainedRealizedFibreNonquadStep` additionally uses the actual retained pairing certificate and the arithmetic realization contribution's retained old Selmer cocycles for detection.

## Precise arithmetic boundary

The following are **not constructed here**:

1. Nonemptiness of the fully strengthened moving-label packet, including every inertness, character, avoidance, precision and coefficient-comparison condition at once.
2. The retained forward/inverse local cochain maps and homotopies from finite continuous local cochains at those genuine primes to the tame models. The matrix-coordinate comparisons proved here do not substitute for them.
3. The arithmetic Tate-basis comparison producing `RetainedTateFrame` for the selected rational curve and the specified number-field Tate basis.
4. The actual finite-prime cup-product comparison producing `RetainedLocalCupStages`, including its scalar inverse data. The transfer theorem is proved, but these matrix congruences are still inputs. This contribution does not claim an unconditional local cup-product identity at the actual primes.
5. The full global finite-stage cochain realization of the retained matrix model, its unchanged old conditions, actual classes and functionals. The degree-one `SelmerRealization` is used as supplied; it is not elevated to a whole-complex homotopy realization.
6. A complete arithmetic producer of the stronger moving-family switching supplier. Exact configured side-data identities and derived stage comparisons are supplied, but the unchanged fixed-place supplier is not reused or declared valid for the moving limit.

No new axioms or printed arithmetic facts are introduced. The deliverable is a checked conditional consumer layer; it is not a completed proof of the remaining arithmetic producers.

## Compiled dependency boundary

The supplied newer integration worktree has built versions of `InnerLimit.Objects`, `InnerLimitArith.Realization`, and `OneProof.RC.FibreDuality.LimitCertificate`. The consumer is checked against those actual interfaces.

The object files for `ZInQKernel.Contrib.OneProof.RC.Uniform.ChebotarevRealization` and `ZInQKernel.Contrib.OneProof.RC.Uniform.ChebotarevTate` are still missing. They were not built. The available Chebotarev and Tate modules and the arithmetic realization contribution were used instead.
