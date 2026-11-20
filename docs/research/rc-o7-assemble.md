# The (O.7) datum on the actual stage

Scoped stop. `datumAt` constructs all five fields of the actual row with
three readings still explicit: `OrbitRead` for the chosen double quotient,
the scalar reduced norm valuation below, and the concrete `ArtinMatch`
projection. The sign equality on the chosen ideal itself is proved.
`actualThetaComparison` and `actualOddStagedInstance` consume these rows
at every admissible index. None of the readings is a comparison of sums
or a theta congruence.

The weights are `ThetaClose.actualPmLocal`, the geometric input is
`PMAdelic.geometricInput` with geometry `PMAdelic.geometry`, and the point
map is `StageKummer.Setup.ev` (the family constructed from `evActual`).
The fixed witness, stage support and precisions are inherited from the
point construction.

The local statement to isolate is the valuation of the reduced norm of the
embedded prime block. For a prescribed conductor-one class representative
(a_c) of the integral ideal (J_c) and a rational prime (p), it is
`valuation (localNrd p ((embedIdeles a_c).val p)) = (absNorm J_c).factorization p`
(the right side cast to `ℤ`). The existing `LocalTorusChart` gives an
isomorphism of unit groups, its rational diagonal, and the criterion for
membership in the conjugated order's units. Its interface has no reduced norm
comparison. A direct proof can match the finitely many valuations above the
given rational prime with a single element of the quadratic field. The ratio
then lies in the integral-unit kernel of the chart, so its conjugate has
reduced norm valuation zero. It remains to identify the reduced norm on that
diagonal element with the quadratic field norm and read its valuation by
the usual residue degrees. This asks about one local element and contains
neither theta coefficients nor CM points.

## Checked adapters

| Lean declaration | Statement and use |
| --- | --- |
| `oddFilter` | `AdmissibleD s D → TorusWeights.OddFilter N s.ell D (-s.weights.m)`, with the partner cast to integers; exposes the filter to norm descent. |
| `requestedIndices` | At the natural index (n), the full filter implies the local support tests with affine parameter ((d-1)/4). |
| `levelFilter` | The full filter implies coprimality with the level and the odd level Jacobi symbols for the support and normalizers. |
| `admissible_of_prepared` | `Prepared`, `GenusPartner`, level identification and the moving Legendre test imply `AdmissibleD`; no additional level or dyadic support input. |
| `ideleToIdeal_eq` | For each finite idele, the two fractional ideal maps are equal, prime exponent by prime exponent. |
| `ideleClass_mk` | The image of the quotient representative under `ideleClassEquiv` equals `toClassGroup` on the same idele. |
| `localNrd_eq` | The torus reduced norm equals the theta reduced norm as a local unit; shared by the two weight factors. |
| `extend_order` | Extending a function by zero through an injection preserves two-power order at each nonzero value. |
| `char_order` | A nonzero value of a quadratic character cast into the target ring has two-power order. |
| `localFactor_order` | Every nonzero value of the actual local Schwartz factor has two-power order. |
| `schwartzFactors` | Reads the actual exceptional local factors and their inverse right-unit covariance from the theta branch, given the local norm factor's value on order units. |
| `stageSchwartzRead` | On nonzero support the stage Schwartz function equals the exceptional product at `Adelic.classRepresentative`; this is the second `StageRead` field. |
| `singleR_same`, `singleR_away` | Inserting one local coordinate into the rational finite ideles gives that coordinate at its prime and one elsewhere. |
| `discCharacter_units`, `discCharacter_trivial` | On integral ideles the discriminant character is the product of the ramified Legendre symbols; it is one if every ramified coordinate is one. |
| `singleR_integral`, `discCharacter_product` | An inserted integral unit has trivial character away from the ramified set; every finite idele's character is the finite product of its inserted-coordinate characters. |
| `mem_bad`, `singleR_unramified` | The ramified set consists of the rational primes dividing the partner; at any other prime the factor is the partner character of that prime raised to its nonnegative valuation. |
| `normFactors`, `normFactors_unit` | The finite norm character supplies the `NormFactors` fields, including triviality on rational quaternions and the order-unit reading used by Schwartz covariance. |
| `stageNormRead` | Reads the actual norm character at `Adelic.classRepresentative`, cast into the coefficient ring. This is the first `StageRead` field. |
| `conductorOne_top` | The conductor ideal at conductor one is the unit ideal. |
| `chiSign_ideal`, `chiSign_of_descent` | On an integral ideal prime to the partner, the selected character's integer sign equals the ideal-norm Jacobi symbol, hence equals the descended norm character on the same conductor-one Picard class. |
| `conductorOne`, `picOne`, `picClass_of_max` | The conductor-one order is maximal; its Picard equivalence sends the usual fractional ideal class of an integral ideal to its conductor-one Picard label. |
| `exists_coprime_class`, `count_at_bad` | Each class has an integral representative prime to the partner; its exponents vanish at every place above a partner prime. |
| `exists_normalized`, `normalized_class` | Every chosen coprime integral representative has an idele inducing exactly that fractional ideal, with blocks equal to one above the partner and the prescribed class. |
| `normalizedIdealRead` | Builds `TorusIdealRead` from these representatives, block-one compatibility for the embedding, and the scalar norm valuation equation. |
| `framePresents` | An orbit specified by an adelic representative presents its vector in the rational frame of the stage's chosen class representative. |
| `tupleBase`, `chartEquiv`, `classFrame`, `OrbitRead` | Define the chart and frame `a_c z_t` from the same choices as the Picard construction, and state the needed equality between that orbit and the output of `OrbitFibers.param`. |
| `torusParametrization`, `torusParametrization_block_one` | Build `TorusParametrization` given `OrbitRead`, and send a normalized input block to one in the quaternion order. |
| `coefficients_eq` | All detecting primes at the fixed level and prescribed signs give the same coefficient ring. |
| `actualStage` | Uses the actual geometry, point detector and weights, with the same least lift as `reference_reduction`. |
| `admissibleAt` | `W.admissible i D` implies the entire `AdmissibleD` record at this stage. |
| `supportBridgeAt` | On the trace-zero sphere in the actual order, the support test is equivalent to half-integrality. |
| `discAt`, `selectedBasis` | The transported selected field has the actual discriminant; its integral quadratic basis is used for support and the reference embedding. |
| `descentAt`, `partnerSymbol` | Norm descent on that field, including the self case at one, and the partner's detecting symbol (-1). |
| `supportAt` | The staged `IntegralSupport` record. Its stabilizer theorem is the one used in the actual coefficient comparison. |
| `datumAtInt`, `actualRows` | Transport the natural row index to the positive integer in the wiring. |
| `thetaComparison`, `oddStagedInstance` | From a family of rows and an independent coefficient reading, apply `thetaComparison_actual` and `StageKummer.toOddStagedInstanceOfReference`. |
| `thetaComparison_chosenRepresentative` | At the same modulus and phase, the raw congruence supplies an integer representative when that representative is free to choose. |
| `stagePrime`, `stageElliptic`, `actualFamily` | Recover the stage instances from the setup and use one coefficient ring for the entire actual family. |
| `actualThetaComparison`, `actualOddStagedInstance` | Specialize the two family wrappers to the actual stage family, deriving coefficient contraction at two from its fixed place. |
| `relabel_sign` | Transport equality of two integer signs along equality of labels and through an equivalence followed by its inverse. |
| `stageReadAt` | The actual norm and Schwartz readings on the common representative supply both fields of `TorusWeights.StageRead`. |
| `orbitsAt`, `weightsAt`, `movesAt` | Use `orbitFibers_of_local` for the orbits, build weights from the checked local factors and supplied torus reading, and apply normalizers to that same orbit map. The orientation equality is definitional. |
| `artinAt`, `datumAtOfIdealRead` | Compose the same ideal label with conductor-one Artin reciprocity and pass the reference orientation, the two pointwise CM identities and the sign matching into `StageKummer.datumAt`. This supplies `reference` and `reduce`. |
| `partner_ne_zero`, `parametrizationAt`, `idealReadAt` | The odd partner is nonzero. With `OrbitRead` and the norm valuation, apply the frame and ideal adapters to the same normalized ideles for the selected field. |
| `datumAt` | The row constructor with the normalized ideles. Its point inputs are the actual selector value, the two CM equations at the common reference orientation and place, and `ArtinMatch` on its computed Artin map and character. Its moving stage test follows from the row's admissibility. |

To wire the conditional result, take `n = D.toNat` at each admissible
integer `D`. Positivity from `admissibleAt` identifies the two indices.
Apply `datumAt` to that row's data and supply the resulting function as
`rows` to `actualThetaComparison` or `actualOddStagedInstance`. For
`PreLeaves.odd_staged` take `Nonempty.intro` of the latter. Neither
consumer requires a separate stage-map family or a coefficient-ring
contraction premise at the actual stage.

## Alignment

* The selector returns a datum on the rational curve. Reduction consumes
  its transport to the integral curve model, `StageKummer.chosenDatum`.
  Build the support basis, reference embedding, Picard labels and Artin
  map from the field of that transported datum. This uses the existing
  curve equality and avoids comparing two dependent field types or asking
  for a second embedding.
* The orbit construction presents a class by (a_c z_t). The theta
  construction reads `Adelic.classRepresentative`; this is a different
  representative of the same class. The frame comparison uses a rational
  left translate and the same right integral unit in the two weight factors.
  The two right factors cancel.
* The normalizer branch tags its stage by the natural discriminant
  parameter cast to an integer, while the reduction branch tags it by the
  negative genus partner. The actual parameter equality and the common
  geometry, order, level weights and least lift identify the data used by
  the two constructors.
* The weight on the chosen frame has a lattice test in addition to the local
  product; the product reading is required only on nonzero support. The
  chosen representatives of the quadratic field's class group must also be
  normalized to coordinate one at the partner primes. Valuation zero there
  does not imply coordinate one.
* At a fixed existing `W.aθ`, the wrapper still needs the theta-side
  phase and integer-representative reading. When the integer representative
  is being defined, `DatumAt.representative` instead supplies one at the
  same precision, after the raw comparison is proved. These are different
  uses of the coefficient interface.

## Remaining hypotheses

| Input | Owner | Kind | Scope |
| --- | --- | --- | --- |
| The fixed `GenusOddInstance W`: newform and periods, Birch–Manin normalization, nonzero rational normalized partner value, prepared filter and genus partner | RC11 / GenusOdd | ELLIOT and existing GLUE prints | Supplies the family of algebraic point data and the level and partner whose splitting is tested. |
| `StageKummer.Setup I L`: chosen prepared witness and its selector value, `ExactWitnessOn`, square fixed detector row and division tower, actual prime sequence, and the `StagesFrom` identifications | Appendix F / rc-stage-kummer and RC0 | ELLIOT and existing GLUE prints | Fixes the geometry and precision of the point side before any theta coefficient is read. `Setup.ev` already supplies every evaluation map. |
| `MultiplierKillsNativeTorsion` at the fixed multiplier `L` | RC23 | ELLIOT and existing Silverman print | Concerns native torsion of the characteristic-zero point data alone. |
| `AdmissibleOddSign W.toRCData` | RC23 | Existing GLUE print (twist root number) | Identifies the sign of the admissible twists; it supplies no coefficient congruence. |
| Fixed level and detecting prime arithmetic for `DiscriminantData`, and the positive level and coprimality used to form the actual order | ThetaClose / actual stage and level data | ELLIOT | Describes the discriminant partner and stage prime, and constructs the level order and local weights. |
| On each admissible row, the actual value of `I.selG D = some t` | rc-param-at-scale | ELLIOT | Specifies a characteristic-zero point datum and its character, with no theta coefficient or congruence. |
| A rational reference embedding of the selected field in the stage quaternion algebra | rc-o7-orbits / Voight | GLUE print already in tree | Embeds a quadratic field once per row; gives no global orbit weights or comparison. |
| `LocalTorusChart` for this embedding, and `HasLocalRealizations` for each orientation | rc-local-torus | missing theory | Completed torus comparison and local realizability; neither asks for a coefficient or any reduced CM point. |
| `OrbitRead` for the normalized class ideles: `param (t,c) = orbitFromRep (a_c z_t)` with the chart and base used by `orbitFibers_of_local` | rc-o7-assemble / Picard quotient computation | missing theory (formal adapter) | A computation of one class label and one orientation. The two class maps are proved equal; reducing the based double quotient to this representative remains open. |
| Reduced norm valuation on the chosen class ideles, as displayed above | rc-local-torus / torus norm compatibility | missing theory | A scalar local valuation equation; no selector, detector or theta side. At primes dividing the partner, both sides are zero by normalization and coprimality. |
| `StageKummer.ArtinMatch` for the computed Artin map and `weightsAt.character` | rc-o7-assemble / character projection | missing theory (formal adapter) | One equality of signs on each class. The two signs agree on the chosen ideal by `chiSign_of_descent`, the ideal's class is `TorusIdealRead.pic_eq`, and Artin followed by its inverse is the original class. The proof joining these dependent projections did not elaborate. |
| `PMAdelic.JetchevKane` and `PMAdelic.SpecialFibre` at each stage; the actual coarse fibre, class identification, Frobenius and Atkin actions | PM adelic geometry | Existing GLUE print and ELLIOT | Describes the quaternion classes and the maps on coarse and residue points, before summation. |
| The identities between the fixed signs `w` and `SpecialFibre.atkinSign`, and cusp annihilation at the level primes by `L` | rc-o7-normalizers / PM adelic geometry | ELLIOT | The fixed Atkin normalization and torsion bound used one level prime at a time. |
| At the reference orientation the actual enhanced CM reduction at each label (c) equals the corresponding coarse ideal-class point | rc-x0-model / PM adelic geometry | ELLIOT (using existing Cornut–Jetchev input) | Equality of individual points of the coarse special fibre. |
| Specialization of that same coarse point equals reduction of the matching Artin conjugate, at the detector's chosen place | rc-x0-model / rc-stage-kummer | ELLIOT | Equality of individual residue points before the detector and character sum. |
| For an independently fixed `W.aθ`, its phase-removed integer coefficient reading in the actual theta stage | Existing coefficient interface / integrator | ELLIOT | Only the name of the theta coefficient as a residue; the reading contains no Kummer or CM term. |

These are smaller statements in the sense of the interfaces: each concerns
strictly less of the construction and none is the comparison on a different
name for the same inputs. This does not claim that a single comparison
congruence logically implies all the structural inputs used to derive it.

The two unfinished formal joins have narrow next steps. For `OrbitRead`,
apply `ideleClass_mk` to `a_c` and reduce the quotient maps on that
representative. In the final based fibre, any representative selected
internally is equal in the double quotient; `orbitFromRep_eq_iff` then
removes that choice. For `ArtinMatch`, project the character field of
`actualWeights` and use `chiSign_of_descent` at `J_c`, transporting along
`pic_eq` and canceling the inverse Artin map. Both are computations of
existing constructions. The scalar norm comparison is the separate
local arithmetic theorem described above. Once these three readings
are supplied, the conditional row constructor consumes them directly.

## Known issues

* The inherited Jetchev–Kane supersingular class input is used at the
  statement and level fixed by the existing geometry interface. The cited result does not cover level one,
  as recorded in the upstream source audit.
* The family requires a selected datum on every admissible row.
  `GenusOddInstance.hselG` ensures `isSome` only with an additional analytic
  rank-one input. The stage's odd sign is not such an input. If the wiring
  allows `none` at an admissible row, the reference-reduction constructor
  does not apply there; a separate vanishing or selector construction would
  be needed. The wrapper does not use a zero stage map to bypass this.
* The bare norm factor is read at the chosen representative; it is the
  product with the Schwartz factor that has the required covariance.
* Literature locators inherited from upstream reports are UNVERIFIED here.
  No printed statement is added.

## Manuscript check

| Tex lines | Step | Verdict |
| --- | --- | --- |
| 8468–8474 | Jetchev–Kane citation | error: the existing source audit records that the cited result does not cover level one. |
| 8495–8578 | Local Schwartz factors, norm twist, and right-unit covariance | gap filled: factor the finite norm character and read both factors at the chosen frame; the lattice test is used on support. |
| 9101–9142 | Use the full odd filter and the actual weighted theta coefficient | OK |
| 9150–9155 | Integral affine generator for the oriented embeddings | gap filled: use the selected datum's field and the existing integral quadratic basis. |
| 9155–9169 | Fibres of oriented embeddings and the representative of each label | unverified: the exact computation `OrbitRead` through the existing Picard quotient remains. |
| 9161–9166 | Integral ideal representatives prime to the partner | gap filled: distinguish the ideal class from its normalized idele. |
| 9171–9179 | Frame change and canceling right-unit characters | gap filled: compare with the adelic class representative used on the theta side. |
| 9180–9194 | Norm character on ideal classes and Artin labels | unverified: the completed block's reduced norm valuation and the last staged Artin sign projection remain. The ideal-norm character identity is checked. |
| 9265–9279 and 8476–8479 | Reference CM point and its specialization | unverified: both pointwise CM identifications remain inputs. |
| 9280–9327 | Detector, stabilizer, weights and phase of the reference contribution | OK, conditional on the specified pointwise and local inputs. |
| 9329–9364 | Level and detecting-prime moves | OK with the existing normalizer constructor and its geometry. |
| 9367–9390 | Orientation count and precision | OK via the existing actual comparison. |

Quotient and representative adapters, restricted-product truncation, the
lattice gate, class normalization and the adapters between the integral
point model and the actual row are on-the-spot (c).

## Verification

Each delivered Lean file was checked separately with `lake env lean`.
The 70 checks in `scratch/rc-o7-assemble/Axioms.lean` reported exactly
`[propext, Classical.choice, Quot.sound]` for every listed declaration
except `relabel_sign`, which uses only `[Quot.sound]`.
No wiring module was edited.
