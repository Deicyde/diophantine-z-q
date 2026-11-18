Scoped stop at Appendix F, tex 9725–9729: the fresh trace computation gives
coefficientwise divisibility, but the constituent field `det_orbit` asks for
membership in the abstract submodule `𝔪Λ`. The manuscript explicitly sets
aside saturation (tex 9644–9646); its coefficientwise identity does not fill
that gap. For example, the coordinate of 2 in the lattice
`Λ = 2ℤ₂ ⊂ ℚ₂` vanishes modulo 2, but `2 ∉ 2Λ = 4ℤ₂`.
This is a gap in the passage to the model's abstract quotient; the
manuscript's coefficientwise identity is valid.

All other requested GLUE fields are proved from the genuine-form and
representation interfaces: `stable_t`, `stable_d`, `finiteIndex`, and
`kummer`. The constructor also derives the chosen-lift `chebotarev`
field from the tree's density theorem. It uses the existing reads and
the out-of-scope `two_fresh` field. No new printed leaf was added.

## Statements and model fields

The namespace below is `ZInQ.Manuscript.RC.TraceLimits`; all new files are
under `ZInQKernel/Contrib/OneProof/RC/TraceLimits/`.

| File and declaration | Statement and field |
| --- | --- |
| `Lattice.coefficientDVR_compact` | The complete rank-one coefficient DVR with finite residue field is compact, by the existing valuation topology theorem. |
| `Lattice.lattice_fg_of_integral_coordinates` | Finitely many integral coordinates detecting vectors give finite generation over the Noetherian coefficient ring. |
| `Lattice.lattice_closed` | A finite submodule of a Hausdorff topological module over the compact coefficient ring is closed. Used by `stable_t` and `stable_d`. |
| `Lattice.residual_closed` | The embedded submodule `𝔪Λ` is closed when the coefficient ring is Noetherian and `Λ` is finite. |
| `Lattice.residual_quotient_finite` | If `Λ` is finite over `O` and `O/𝔪` is finite, then `Λ/𝔪Λ` is finite. Used by `finiteIndex`. |
| `Lattice.residual_isOpen` | Under those conditions, `𝔪Λ` is open in `Λ`. Used by `finiteIndex`. |
| `Density.dense_arithmeticFrobenius` | All arithmetic Frobenius lifts at primes outside a finite set are dense in the Krull topology. Uses the tree's `frobDense` with its proved Chebotarev. |
| `Density.isOpen_rightPeriods` | For a continuous map from a compact group, its simultaneous right periods modulo an open additive subgroup form an open set. Compact projection argument, on-the-spot (c); used by `finiteIndex`. |
| `Limits.dense_frobeniusTests` | Restrict density to good primes, with any additional finite avoidance set. |
| `Limits.frobenius_conj_in_constituents` | Two lifts at a prime unramified in the constituents have images conjugate by a common Galois element. |
| `Limits.dV_conj` | The scalar determinant operator is conjugation invariant. |
| `Limits.operators_eq_at_frobenius` | At good unramified primes the trace and determinant operators are independent of the choice of lift. |
| `Limits.continuousOperators_of_matrix` | Continuity of the matrix entries of each constituent gives pointwise continuity of trace and determinant on the lattice. |
| `Limits.stable_operators` | A closed integral module preserved by its good Hecke and diamond operators is preserved by all continuous scalar trace and determinant operators. Gives `stable_t` and `stable_d`. |
| `Open.consN_isOpen` | Continuous trace evaluation, open reduction kernel and continuous type give openness of `consN` for every finite `U`. Via `subgroup_isOpen_iff` this is the fixing-field assertion in `GalNOpen`, identified by `consN_eq_galN`. |
| `Open.galNOpen_of_consN_open` | The open constituent subgroup gives the same finite fixing-field condition as the tree’s `GalNOpen`, by `consN_eq_galN`. |
| `Open.consN_finiteIndex` | Open `consN` has finite index. Gives `finiteIndex`. |
| `Open.inertia_le_consN` | Good-prime inertia outside `U` and the constituents' support is contained in `consN` for good `U`. This is the `consN` analogue of `GalNUnramified`. |
| `Open.consN_chebotarev` | For good `U`, openness and this inertia condition give the model's chosen Frobenius representative modulo `consN`, up to conjugacy and avoiding any finite set. Gives `chebotarev` from the tree. |
| `Fourier.diamond_correction_integral` | If two character values differ by a sign, their difference times the shell coefficient is divisible by integer two in `O`. |
| `Fourier.fresh_mul_ne_unary` | If a prime divides neither the index nor the unary subscript, multiplying the index by it leaves the unary support. |
| `Fourier.unary_fresh_trace` | At an index `n`, the `T_q` coefficient of a reduced unary correction with subscript `J` vanishes when `q ∤ nJ`. |
| `Fourier.diamond_fresh_trace_coeff` | The same vanishing applies to the traced diamond discrepancy at a fresh good pair, using its correction formula. |
| `Determinant.detOrbit_coefficient` | The coefficient of `(d(u)−1)t(v)F_U` lies in `𝔪` at every positive index and all `u,v`, provided the Fourier data and coordinate continuity. This is the coefficientwise part of `det_orbit`. |
| `Elementary.normal_of_all_squares` | A subgroup containing every square is normal. |
| `Elementary.exists_quadratic_separating` | An element outside the join of the subgroup generated by the squares and `N` is detected by a quadratic character trivial on `N`. On-the-spot (c) via a vector space basis of the quotient. |
| `RadicalWitness.squarefree_radical_of_open_ker` | A quadratic character with open kernel is the action on a square root of a squarefree integer. On-the-spot (c), using an anti-invariant in the fixed field. |
| `Quadratic.sqrtChar_eq_one_of_support` | Triviality on `−1` and the listed primes implies triviality on every integral radical supported on the list (include 2). |
| `Quadratic.radicalKernel_finiteIndex` | The quotient cut out by the listed radicals is finite. Does not assert maximality among elementary extensions of that support. |
| `Quadratic.radicalKernel_le_squares_sup` | Classification of the quadratic characters trivial on `N` by supported radicands implies that the radical kernel lies in the join of the squares and `N`. |
| `Quadratic.sqrtChar_trivial_on_inertia_of_units` | A radical character is trivial on inertia where two and the radicand are units in the residue field. |
| `Quadratic.supportedQuadratic_of_inertia` | Openness and unramifiedness of the subgroup imply supported classification given the odd-divisor inertia comparison. |
| `Quadratic.sqrtChar_prime_of_bit` | A trivial bit at `p` and trivial sign imply triviality on the radical `p` since `p* = (−1)^(p/2)p`. |
| `Quadratic.kummer_of_support` | Type coverage and supported-character classification imply the exact requested `kummer` conclusion. |
| `InertiaLift.map_inertia_of_profinite` | Under a profinite invariant kernel, inertia maps onto the inertia of the contracted prime. On-the-spot (c), adapting the finite proof with profinite residue stabilizers. |
| `InertiaLift.ramificationIdx_two_le_of_square` | If a squarefree integer divisible by a prime has a square root in the containing ring of integers, a prime over that divisor has ramification index at least two. On-the-spot (c), by ideal multiplicities. |
| `AbsoluteInertia.absolute_inertia_maps` | Absolute inertia in the integral closure maps onto the inertia at the contracted prime in a finite Galois subextension. On-the-spot (c), using the fixed-field invariant ring. |
| `AbsoluteInertia.oddRadicalRamification` | For an odd prime dividing a squarefree radicand, absolute inertia at a prime above it moves its square root. Discharges the comparison used in `supportedQuadratic_of_inertia`. |
| `TypeSupport.sqrtChar_eq_kChar` | For `4|k| ∣ m`, the fixed radical character of `k` factors through `typChar m` on all of `G_ℚ`. On-the-spot (c), by matching Frobenius on a finite compositum. |
| `TypeSupport.typChar_detects_radicals` | The residue-squareclass type for a modulus divisible by four and by `4p` for each support prime detects the stationary radicals. |
| `TypeSupport.stageChar_detects_radicals` | The extra stage bit detects the added stationary radical, using the sign already detected by the residue-squareclass type. |
| `Model.consN_supported_of_ramification` | The inertia containment for a good set reduces the remaining support condition on `consN` to the odd-divisor inertia comparison. |
| `Model.consN_kummer_at_good` | For good `U`, trivial type and bits imply membership in the join of the squares and `consN`, using absolute inertia and the proved character classification. Gives `kummer` on good sets. |
| `Model.consN_kummer_of_good` | Extending the form family by zero off good sets carries the good-set conclusion to all finite sets. On-the-spot (c). |
| `Model.buildConstituentModel` | Assembles the unmodified model with the full field statements, with the determinant comparison and the named genuine data below. Its existing `Inputs` remain applicable verbatim. |

## Inputs for the genuine construction

- Tex 9638–9665, 9649–9654, 9762–9797: the finite constituent family including old multiplicities, algebra over the coefficient ring at two, `Λ` finite, compact coefficient DVR with finite residue field and closed maximal ideal, genuine `F_U = θ H_U`, coefficient-one `read`, chosen arithmetic Frobenius lifts, and `ρ` from the cuspidal Carayol representations and Eisenstein pairs. The compactness in `lattice_closed` is the compactness of a complete DVR with finite residue field, not of arbitrary complete DVRs.
- Tex 9655–9668, 9795–9796: `GoodOperators` supplies `O`-linear good Hecke and diamond operators on `Λ` realizing `tV ρ (frob q)` and `dV ρ (frob q)`; the latter is `q` times the diamond operator. `ContinuousOperators` is pointwise continuity of both scalar actions. `UnramifiedConstituents` is triviality on inertia at good primes off the finite support, simultaneously for the retained constituents (tex 9524–9554, 9762–9797). Here good test primes omit both the modulus and the specified exceptional primes.
- Tex 9655–9662, 9719–9727: `DeterminantFourierData` supplies the good Hecke recurrence, reduced unary support using `θ ≡ 1`, and the diamond discrepancy as a coefficientwise integral sum of the undivided corrections, up to the scalar term, which vanishes coefficientwise modulo `𝔪`. This does not require each unary correction to lie in `Λ`. Fourier coefficient evaluation on the embedded lattice is continuous.
- Tex 9725–9729: `DetectsDetOrbit` is the missing comparison restricted to these discrepancy vectors. If every positive Fourier coefficient of such a vector lies in `𝔪`, the vector must be in `𝔪Λ`. The smallest useful proof is an explicit expression in `𝔪` times the chosen generators for these vectors, or injectivity of coefficient reduction on their images alone. Global saturation would be sufficient but is not assumed. A coefficient-saturated replacement lattice would require a separate compatibility proof with the original model and its two readings.
- Tex 2016–2029, 2162–2163 and 9745–9750: select a fixed support `S` containing two, the prime divisors of the type modulus, and the constituent exceptions. `TypeDetectsRadicals` says that the type kernel fixes the radicals of `−1` and the primes in `S`. The code proves this for `typChar` when the modulus contains the necessary factors `4p` (eight for two), and for `stageChar` with its extra prime. `OpenTypeKernel` and `IsTypeChar` record continuity and the type reading; the tree supplies them for those same types. For nongood sets the family uses zero forms, as the manuscript's construction only supplies forms on good sets.
- Tex 9741–9745: `two_fresh`, the abstract reduced double trace vanishing, is outside this run. Tex 9671–9704 and 9905–9918: supply the unchanged `Inputs` (`reading` and `o12`) to `toGaloisTraceModel` for the constructed model.

## Verification

All 13 files compiled with Lean under the `lake env` environment. The 45
dependency audits returned only
`propext`, `Classical.choice`, and `Quot.sound`. The interrupted build handoff
allowed a prerequisite build and a proof check to overlap. The final checks
waited for the prerequisite build to finish and used one serial invocation
at a time.

## Known issues

- Tex 9725–9729 only gives a statement about reduced Fourier expansions.
  Reading it as vanishing in the abstract quotient is invalid without a
  comparison. The same distinction applies to the use of `two_fresh`, which
  is outside scope. No new assertion is made about the constant coefficient.
- The elementary extension being finite does not by itself identify its
  characters. The checked proof uses the open subgroup, the action on a
  squarefree radical, and the finite-to-absolute inertia comparison.
  The type coverage requires the full stationary support, including two.
- The base's build cache contained a stale `Hypotheses/Pole.olean` with the
  earlier polynomial. The proof at `Hypotheses/PoleManuscript.lean:42` did not
  check against that cache. Rebuilding the checked-out source in a separate
  artifact directory fixed this mismatch; source files outside the new
  directory were not changed.
- Carayol is used in the model's convention in tex 9773–9797; the manuscript
  locator is §§0.3–0.7, Theorem A, pp. 409–411 (source pagination
  UNVERIFIED). No independent print statement was added.

## Manuscript check

- Tex 2016–2029, 2162–2163 — OK: the unit squareclasses and added stage bit detect the stationary radicals at the specified support.
- Tex 9524–9554 — unverified: the bad support is prescribed by the genuine levels; the subgroup inertia containment is proved from this representation input.
- Tex 9638–9646 — OK: integer divisibility precedes reduction; the two reduced objects must be distinguished.
- Tex 9647–9654 — unverified: genuine theta products and their constituent decomposition are not supplied by this run.
- Tex 9655–9659 — OK: the sign ratio gives integral division by two; the genuine character formula is input.
- Tex 9660–9662 — unverified: the recurrence and preservation on the chosen translate lattice are supplied by the genuine forms.
- Tex 9663–9665 — OK: finite integral coordinates give a finite module over the coefficient DVR; compactness gives closedness.
- Tex 9666–9668 — gap filled: compare arbitrary and chosen lifts using inertia, then apply density to closed preimages.
- Tex 9663–9668 (finite quotients) — gap filled: the right-period condition over all base elements is open by compactness and discreteness of lattice reduction.
- Tex 9671–9704 — unverified: the coefficient-one reading and precision bound are genuine-form inputs.
- Tex 9706–9708 — OK: positive unary support gives the fresh coefficient vanishing once the genuine formulas are supplied.
- Tex 9712–9717 — OK: the avoidance set can depend on the tested index; the determinant proof uses this at two test primes.
- Tex 9719–9724 — OK: the scalar and correction terms give the good-prime diamond discrepancy formula, conditional on the stated Fourier data.
- Tex 9725–9729 — error: the implication to the abstract residual orbit would need a separate comparison; the coefficientwise computation is valid.
- Tex 9730–9739 — OK: the matrix identity and trace of the identity are already in the tree; their use in the abstract quotient requires `det_orbit`.
- Tex 9741–9747 — unverified: the two-fresh abstract reduction is outside scope.
- Tex 9748–9750 — gap filled: open quadratic characters are squarefree radicals, and inertia over an odd divisor moves the radical by finite ramification and the absolute restriction theorem. The stationary type and the added bits detect the resulting finite elementary quotient.
- Tex 9762–9771 — OK: multiplicity spaces carry scalar trace and determinant; continuity and Frobenius evaluation are stated for those operators.
- Tex 9773–9797 — unverified: the cited theorem and its normalization supply the representations and compatibility; no new print.
- Tex 9905–9918 — unverified: the `o12` genuine coefficient reading is unchanged.
- Tex 9919–9921 — OK: the tree's Chebotarev theorem applied with openness and inertia gives the chosen-lift quotient statement.
