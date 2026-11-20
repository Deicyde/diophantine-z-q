# Closing the actual (O.7) row

`datumAtActual` constructs the support, orbit parametrization, weights,
normalizer moves, and comparison at the chosen reference orientation of
the actual (O.7) row. The local charts and orientation realizations are supplied by
`LocalTorus`. The orbit, reduced norm and Artin character readings are
proved on the chosen representatives. At a selected row the remaining
proof inputs are `ht`, `hCM`, `hπ`, `hSign` and `hCusp`, with the
existing fixed stage data. No coefficient reading is needed to construct
a row.

`oddStagedActual` takes these inputs over the admissible integers at every
stage, builds the rows at `n = D.toNat`, and returns
`Nonempty (OddStagedInstance W)`. This is the type of
`PreLeaves.odd_staged`. The wrapper also uses the existing torsion and
odd-sign inputs and the independent phase reading for the fixed
`W.aθ`. No wiring changes or new prints are needed.

The stage uses the full odd filter: `D > 0`, `D` squarefree and prime
to the partner, and moving symbol `+1`; `D h_*` is an odd fundamental
discriminant and its field splits at every prime of `2N`. The fixed
partner symbol is `-1`. In Lean, `admissibleAt` and `partnerSymbol`
supply these facts from the admissible index and fixed data.

The manuscript uses a conductor-one point on every admissible row,
including the torsion rows. The present selector interface does not yet
guarantee this coverage.

## Known issues

* **Selector coverage.** Tex 8209–8217 defines the point on the whole
  filter; 9265–9279 uses its actual reference CM point. Tex 8298–8306
  applies the fixed multiplier on every row, and 9417–9419 and
  9439–9443 explicitly treat rows without a simple zero. Neither the
  reference CM point nor its Artin conjugates require analytic rank one.
  `GenusOddInstance.hselG` presently guarantees a value only with
  `AnalyticRank (qtwist (Ecurve ℓ) D) 1`. For the fixed instance, the
  minimal extra coverage statement is
  `∀ i D, W.admissible i D → (I.selG D).isSome`. It asserts coverage of
  the chosen selector, not nonvanishing. It cannot follow for an
  arbitrary selector that was allowed to be `none` on these rows.
* **Inherited source scope.** Tex 8468–8474 describes all levels prime to
  the stage prime. As recorded in the upstream source audit, the cited
  Jetchev–Kane result does not cover level one. The existing geometry
  interface remains an input. Source locators inherited from the
  manuscript and prior reports are UNVERIFIED here.
* **Existing path for filling the selector.** Tex 2915–2917 chooses the
  CM point on `X₀(N)` over its ring class field by proper ideal lattices
  and fixed orientations, then applies the modular parametrization.
  The missing Lean realization for an empty admissible entry is
  `StageSelector.PreparedParamValue` at the chosen conductor-one
  form: an embedding of its ring class field into `ℂ` and a point over
  that field whose complex image is `phiAn` at the fixed scale. The
  field, form and character are already constructed. The existing
  `StageSelector.exists_selected_of_admissible` fills these holes for
  an extended selector and preserves the witness. Alternatively,
  `Gz34Instance.selectGenus_isSome` covers the whole prepared filter
  when building the instance with its algebraic value input. Neither
  theorem identifies an independently fixed `I.selG` with the new
  selector; the integrator must use a choice that supplies the required
  selector equations.
* **Dependent Artin projections.** A direct proof through
  `weightsAt.character` and the chosen Galois label exhausted Lean's
  definitional-equality budget, unfolding the transported curve and
  ring class field. The proof first compares integer signs on `J'.pic c`,
  then uses separate lemmas for the cast and for inverse Artin. The
  cancellation uses the composition law for equivalences with the
  model transport and reciprocity map kept opaque during elaboration.
* **Reference origin.** The row compares the CM labels with the chosen
  `tupleBase` on the reference orientation. Knowing just that the
  CM and quaternion points have the same orientation does not pin down
  the identity ideal class. The pointwise inputs must identify the
  origin and the Artin-labelled conjugates at the detector's place, as
  tex 9272–9279 requires. This run does not identify those points.

## Statements

All declarations below are in `ZInQ.Manuscript.RC.O7Residual`. Write
`F` for the field of `StageKummer.chosenDatum t`, `J_c` for
`coprimeIdeal … c`, `a_c` for `normalizedIdele … c`, and
`z_b` for `tupleBase … b`. The index of a natural row is
`n : ℕ`, interpreted as `(n : ℤ)` by the stage.

| Declaration | Statement and input supplied |
| --- | --- |
| `chartAt`, `realizationsAt` | `LocalTorus.localTorusChart` and `LocalTorus.hasLocalRealizations` at the selected integral basis and rational embedding. The unit and affine generator are definitionally those of `PicardFibers`; no transport or placewise assumptions. |
| `ideleOrbitEquiv_toClassGroup` | The image of `toClassGroup … a` under the based idele orbit equivalence is the double class of `e(a) z_b`, by `ideleClass_mk` and the quotient maps on a representative. |
| `basedFiberEquiv_mk` | The based fibre equivalence on the double class of `g z_b` has underlying orbit `orbitFromRep (g z_b)`. The internal representative has the same double class, so `orbitFromRep_eq_iff` removes that choice. |
| `orbitRead`, `orbitReadAt` | For a family of ideles reading their prescribed ideal classes, `param (b,c) = orbitFromRep (e(a_c) z_b)`; `normalized_class` specializes it to the actual stage and choices. Supplies `hr`. |
| `absNorm_factorization_eq_of_counts` | For nonzero integral ideals with equal exponents at all places above `p`, the absolute norms have equal `p`-exponents. A place above `p` contributes its ideal exponent times the residue degree; all other places contribute zero. |
| `exists_integer_of_block` | An integral block of local field units over `p` has the same valuations as one nonzero integer of `F`. The valuations are locally constant at the nonzero coordinates and the global integers are dense in the product of completed integer rings. |
| `adicOrd_integer` | At a finite place the negative valuation logarithm of a nonzero global integer is the exponent of its principal ideal. |
| `nrd_embedding` | `nrd (ι x) = Algebra.norm ℚ x` for the reference quadratic embedding. Quaternion conjugation negates the trace-zero generator, so it restricts to the quadratic involution. The determinant of multiplication is the quadratic norm. |
| `block_norm_valuation` | If a finite idele induces the nonzero integral ideal `J`, the valuation of the reduced norm of its chart image at `p` equals `(Ideal.absNorm J).factorization p`, cast to integers. Divide by the diagonal approximation and apply the chart's integral-unit test. Conjugation preserves the reduced norm, and the reduced norm of a completed order unit has valuation zero. |
| `normalized_norm_valuation` | The same equality for `a_c,J_c` at every `p`. At partner primes the block is one and coprimality makes the ideal norm exponent zero. Supplies `hnorm`. |
| `character_eq_on_class` | For a common Picard class `pic c` represented by `J_c`, the integer sign from norm descent equals `chiSign χ (pic c)`. Apply `chiSign_of_descent` and transport along `pic_eq`. |
| `actual_character_projection` | The weight character at `c` is the coefficient ring cast of the integer descent value at `J'.pic c`. |
| `inverse_after_trans`, `actual_artin_projection` | Applying the inverse of a multiplicative equivalence to a label produced by postcomposing with that equivalence recovers the original label. At the actual stage this gives `Artin⁻¹ (artinAt c) = J'.pic c`. |
| `artinMatchAt`, `artinLabelAt` | The actual character projection is the cast of the norm descent sign on the same class. Its inverse Artin label is `pic c`. For the normalized ideal read, the label is just conductor-one reciprocity on `picOne c`. Supplies `hχF`. |
| `datumAtActual` | `DatumAt (actualStage …) (n : ℤ) (lamOf W.Mθ L I.selG s.ev i (n : ℤ))`, from the fixed data and `ht,hCM,hπ,hSign,hCusp`. Supplies all five fields via the existing actual row constructor. |
| `PointInputs`, `admissibleNatAt`, `actualRowFamily` | Bundle the selector and pointwise hypotheses (with the chosen datum, embedding, orientation and coarse point family); transfer the full odd filter to `D.toNat`; construct one actual natural row for each `W.admissible i D`. |
| `oddStagedActual` | `Nonempty (OddStagedInstance W)` from that family and the existing fixed-coefficient phase reading, native torsion bound and odd-sign input. The type is the field `PreLeaves.odd_staged` on the integration branch. |

## Remaining hypotheses

These inputs each concern a proper part of the comparison. In particular,
none states a congruence with a CM sum on one side and a theta coefficient
on the other. This is an interface scope claim, not an implication from
the final congruence to its construction data.

| Input | Owner | Why smaller than (O.7) |
| --- | --- | --- |
| `GenusOddInstance W`, `StageKummer.Setup I L` | RC11 / GenusOdd and Appendix F / stage Kummer | Fix the modular parametrization, partner, witness, detector, selected places and retained precisions. `Setup.ev` supplies the family of evaluation maps. Neither names a theta coefficient comparison. |
| `hN,hcop,H,w,hm` at the actual stages | ThetaClose and fixed stage arithmetic | Specify positive level, disjoint detecting prime, weight signs and discriminant data with (m=-h_*). `admissibleAt` derives the full odd filter from the wiring; `partnerSymbol` reads the fixed inert symbol. |
| `PMAdelic.JetchevKane`, `PMAdelic.SpecialFibre` | PM adelic geometry | Identify the coarse classes and provide specialization, Frobenius and Atkin maps on individual geometric points. |
| Chosen rational embedding `ι` for the selected field | O7Orbits / existing Voight print | A local-to-global embedding alone gives neither a choice of CM origin nor any comparison. `exists_reference_embedding` obtains it from the existing `Voight1467VToIII` input, the field condition at infinity and the two detecting symbols. |
| `ht : I.selG (n : ℤ) = some t` for each admissible row | rc-param-at-scale / selector integration | Specifies one characteristic-zero datum, its form and character. The selector cannot be assumed total from the current rank-one guarantee. |
| `hCM` on the reference orientation | rc-x0-model / Cornut–Jetchev | Identifies each actual enhanced CM reduction with the corresponding coarse ideal-class point. It states an equality of individual points. |
| `hπ` at the chosen place | rc-x0-model / stage Kummer | Specialization at each coarse label equals reduction of that Artin conjugate, before evaluating the detector or summing. |
| `hSign,hCusp` | O7 normalizers / PM adelic geometry | Identify the existing Atkin signs and say that (L) annihilates the cusp translations. Each is a statement at one level prime. |
| `MultiplierKillsNativeTorsion` and `AdmissibleOddSign` | RC23 / existing torsion and root-number inputs | Control torsion and twist signs without using the theta coefficient. These are for the odd instance, not for the per-row comparison constructor. |
| Phase and integer representative reading for fixed `W.aθ` | Theta coefficient interface / integrator | Identifies a fixed integer with the phase-removed actual theta coefficient modulo the given precision. No CM term, detector output or weight sum on Picard labels enters this premise. The underlying comparison row is independent of it. |

## Manuscript check

| Tex lines | Step | Verdict |
| --- | --- | --- |
| 2915–2917, 8209–8217 | Choose conductor-one CM points on the whole filter | OK: ideal lattices and the split Heegner condition precede any rank restriction. |
| 8298–8306, 9417–9419, 9439–9443 | Apply the multiplier also to torsion rows | OK: simple zero is used for nontorsion and the index, not for the existence of `x_D`. |
| 8372, 9205–9208 | Partner symbol and inertness of the product at the stage prime | OK: the moving symbol is (+1), the partner symbol is (-1). |
| 8468–8474 | Jetchev–Kane reference | error: inherited source audit records that the cited result omits level one. |
| 8476–8479 | Extend the modular parametrization at good reduction | unverified: the corresponding pointwise identity remains `hπ`. |
| 9105–9113, 9119–9142 | Full odd filter and completed local orientations | OK: the filter is read from admissibility, and the existing local realization theorem is applied to that filter. |
| 9150–9155 | Rational reference embedding | unverified: the existing Voight print is used as the source for the chosen embedding. |
| 9155–9169 | Based Picard torsor and its class representative | gap filled: evaluate the quotient maps at the normalized idele and remove their internal representative choice (c). |
| 9171–9179 | Frame change from the chosen torus representative to the theta representative | OK: the existing frame adapter uses the orbit equality and the same rational and right-unit factors. |
| 9180–9189 | Reduced norm equals field norm on the torus; read its exponent at a rational prime | gap filled: use a simultaneous approximation and the integral-unit test, and weight the prime-ideal exponents by residue degree (c). |
| 9190–9194 | Prime-to-partner normalization and Artin sign | gap filled: partner blocks are one, use coprimality for the zero valuation, and match the two signs on the same Picard class before cancelling Artin (c). |
| 9265–9279 | Match the reference orbit and place to the actual CM point | unverified: the two pointwise CM inputs are outside this run. |
| 9280–9327 | Reference evaluation and actual weights | OK conditional on the fixed geometry, selector and pointwise inputs. |
| 9329–9364 | Normalizer moves | OK conditional on the fixed Atkin signs and cusp annihilation. |
| 9380–9398 | Fixed integer theta representative with the same precision | unverified for the existing `W.aθ`: its independent coefficient reading remains an input of the odd-staged wrapper. |

## Verification

All seven new Lean modules compiled individually with `lake env lean`:
`IdealNorm`, `ReducedNorm`, `OrbitQuotient`, `Orbit`, `Artin`, `At`,
and `Family`. The runs were serial. The [check file](../../scratch/rc-o7-residual/Axioms.lean)
audits all new named declarations, including the data constructors.
In the [output](../../scratch/rc-o7-residual/axioms.txt),
`inverse_after_trans` uses only `Quot.sound`; every other checked
declaration uses `propext`, `Classical.choice`, and `Quot.sound`.
