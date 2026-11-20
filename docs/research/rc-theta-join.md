**Scoped stop.** The Appendix F join constructs the specified Schwartz
product, the reduced-norm idèle character, the scalar phase and its
multiplicative extension, and the finite trace-zero frames on the
explicit level order. `levelPmLocal`, `levelStage`, and `levelValLift`
assemble these objects and call the existing consumers, conditional on
the local comparisons for the individually indexed neighbour. The
actual norm covariance is proved under the manuscript's discriminant
disjointness assumptions. There is no unconditional inhabitant of
`PMLocal` in this change. The neighbour sum follows from the local
lattice statement; `levelPmLocal` assumes no equality of theta
coefficients.

The coefficients are generic in the integral ring and in the chosen
level characters, so the construction takes the actual
`LocalWeights.coefficientRing K v` with `v` above two.
`LocalWeights.coefficientRing_two` is the existing integer contraction
theorem. No extra sieve is included. The local split chart at a positive
dyadic level uses the same affine level weight as at the other level
primes, with the character reduced mod four. At dyadic level zero it
uses the separate unweighted dyadic factor.

## Formal statements

Here `z` denotes a finite adelic representative of the indicated ideal
class, `R_z` its rational left order, and `A.places` the exceptional
primes. Declarations are under `ZInQ.Manuscript.RC.ThetaJoin`. Each row
gives the statement in mathematical notation and its use in `PMLocal`;
the support results are separate and do not change the structure.

| Declaration | Statement and field supplied |
| --- | --- |
| `matrix_mul_complement`, `split_invariants` | For a two by two matrix, (X(tr X-X)=det  X) as a scalar; in a split quaternion chart trace is (2x.re) and determinant is `(x * star x).re` (`f`, `frame.coord_det`). |
| `integralMatrix_injective`, `split_image`, `splitOrderEquiv_apply` | Entrywise casting is injective, the completed level order maps onto the standard order at exponent (v_p(N)), and the integral equivalence commutes with the ambient chart (`f`, `frame`). |
| `divisionCompletion` | The level completion at the detecting prime is the completed explicit maximal order. `splitIdentification` includes the cyclic quotient action; `divisionIdentification` reuses the division chart (`f`). |
| `mem_support`, `mem_exceptionalPlaces` | The support of the phase is the natural-prime image of its places; the actual places are exactly the primes dividing (2mNℓ₀) (`support`). |
| `natUnit_val`, `away_mul`, `away_one`, `away_of_not_mem` | Away integers give the indicated local units; a product is away iff each factor is; one is away and a prime outside the support is away (`s`, `ηMul`, `ηOne`). |
| `scalar_mul`, `scalar_order`, `phase_good`, `phase_unit`, `phase_order` | The finite product of `α_q` is multiplicative on away integers and killed by a common two-power; its good-prime value is `phase`, whose inverse and two-power order give `sUnit`, `sOrder`. |
| `eta_one`, `eta_mul`, `eta_good` | The extension by zero times the Jacobi character is normalized, multiplicative, and has the required good-prime value (`ηOne`, `ηMul`, `ηGood`). |
| `scalarSign_sq`, `unaryParity_odd` | The scalar phase at minus one squares to one, and its sign times the odd discriminant sign and ((-1)^i) is minus one for the selected (i ∈ {0,1}) (`parity`). |
| `weightAt_of_local`, `latticeSphere_finite`, `weight_finiteSupp` | Integral local membership opens the product gate; the norm sphere on the rational left lattice is finite by definiteness; the weight's nonzero part is a subset (`f`, `finiteSupp`). |
| `weightAt_zero`, `coefficientAt_zero` | A zero exceptional factor kills the weight at zero, and the definite trace-zero sphere of norm zero is a singleton (`thetaZero`). |
| `atRep_left`, `weightAt_left`, `coefficientAt_left` | A rational left translate is accompanied by conjugation of the rational vector, preserving its local coordinates, weight and reindexed sphere sum (`frameNb`). |
| `localUnit_conj_mem`, `atRep_right`, `weightAt_right` | Order units preserve membership; a right translate conjugates each local coordinate and multiplies its global weight by the product of inverse local norm-character factors (`f_conj`, `frameNb`). |
| `atRep_nsmul`, `localUnit_smul_cancel`, `weightAt_scale` | Multiplication by a natural commutes with adelic translation, a local unit times its inverse acts trivially, and on the left lattice an away integer multiplies the weight by the product of the local scaling factors (`frameScale`). |
| `weightedAt_change`, `weightedCoefficient_eq`, `weight_conj` | Local covariance and the two norm restrictions imply pointwise cancellation on the right, descent of the weighted coefficient on both sides, and class-order-unit conjugation invariance (`frameNb`, `f_conj`). |
| `levelExponent_pos`, `legendre_two_power`, `re_unit_smul_iff` | A level factor at a prime dividing (N) has positive exponent; quadratic factors obey the common two-power bound; unit scaling preserves the trace-zero test (`f`, `sOrder`, `frameScale`). |
| `divisionFactor_zero`, `schwartz_zero` | The division residue weight vanishes at zero, hence so does the actual global constant coefficient (`thetaZero`). |
| `splitFactor_scale`, `divisionFactor_scale`, `localFactor_scale` | Every actual local factor scales by `localAlpha`, with the dyadic affine rule included (`frameScale`). |
| `schwartz_finiteSupp` | The actual Schwartz weight has finite support on each rational trace-zero norm sphere (`finiteSupp`). |
| `re_conj`, `splitUnit_ambient`, `dyadic_conj_of_zero`, `splitFactor_conj` | Local trace is conjugation invariant, the split order unit has the same ambient matrix, and split weights obey their local conjugation laws, including both dyadic cases (`f_conj`). |
| `divisionFactor_conj` | A completed order unit acts trivially on the division factor (`f_conj`). |
| `val_rationalPrime`, `rationalPart_support`, `rationalPart_pos`, `rationalPart_valuation` | The valuation of a rational prime is the corresponding Kronecker delta; the product of primes to the idèle valuations is finite, positive, and has the same valuations (`χN`). |
| `normalized_valuation`, `integralUnit_val`, `localUnitPart_val`, `rationalPart_of_units` | The normalized coordinates have valuation zero, are identified as local integer units, and normalization fixes everywhere integral units. `discriminantCharacter` multiplies the Legendre factors as a monoid homomorphism (`χN`). |
| `positive_rational_unit`, `rationalPart_diagonal`, `discriminantCharacter_diagonal` | A positive rational unit with trivial valuations is one; the rational valuation part of the diagonal of a positive rational is that rational, and its discriminant character is one (`χN`, `frameNb`). |
| `norm_toLocal`, `norm_atRep`, `completion_norm_integral` | Reduced norm commutes with completing and conjugating; on the explicit local orders it is integral (`χN`, `frame`). |
| `val_localNorm_of_orderUnit` | An order unit and its inverse have integral norms, hence its norm has valuation zero; `normIdeles` and `levelNormCharacter` define the stated pullback (`χN`). |
| `normUnit_val`, `normCharacter_integral`, `normCharacter_diagonal`, `splitUnit_norm` | The integral norm unit casts to the local reduced norm, the character on integral order units is the product of its ramified Legendre values, its value on rational diagonals is one by definiteness, and the determinant of a split order unit is its norm unit. With discriminant disjointness, `levelNormCovariance` gives the matching inverse character on every conjugated local factor (`f_conj`, `χN`, `frameNb`). |
| `levelNormCharacter_single` | A one-place step of reduced norm valuation one at a good prime p has character `jacobiSym (-m) p` for squarefree m ≡ 3 (mod 4). The normalized units at primes dividing m are the local images of p⁻¹, and the existing reciprocity calculation identifies their product (`frameNb`). |
| `nrd_nsmul`, `mem_vectors`, `residueRep_cast`, `det_equation` | Norm scales by (p^2); frame vectors enumerate the indicated norm sphere; entry representatives recover their residues; the trace-zero matrix determinant is (-a^2-bc) (`frame`). |
| `coord_det`, `coord_scale`, `dvd_entry`, `div_vector` | The coordinates give the determinant and scaling congruences mod (p^2); divisibility of the three entries forces entrywise divisibility and a rational lattice preimage (`frame`). |
| `atRep_re`, `atRep_rat_smul`, `embed_matrix`, `cast_matrix`, `divisible`, `lattice_norm_integral` | The local chart respects trace and rational scalars, uses the integral matrix of the translated vector, is saturated under division by (p), and has natural integer norms (`frame`). |
| `coefficientAt_eq_vectors`, `frame_theta`, `frame_scale` | The rational coefficient is the reduced lattice sum, equal to the frame theta coefficient, and the reduced weights obey the chosen scaling law (`frameTheta`, `frameScale`). |
| `atRep_single_away`, `weightAt_neighbour_scale`, `frame_neighbour` | Away from (p) a one-place step changes no coordinates. The original weight on (px) is (s(p)) times the neighbour weight on (x); summing the vector bijection gives (s(p)^{-1}) times the actual `nbrSum` (`frameNb`). |
| `good_not_dvd`, `good_away`, `good_not_two`, `good_not_dvd_m`, `level_neg` | Good primes avoid the specified factors, and the second algebra parameter is negative (`away`, `neTwo`, `goodM`, `hb`). The existing `LineIndex.lineIndex` supplies `lines`. |
| `weightedNeighbour_of_transport` | The indexed neighbour's class, vector, and norm comparisons imply the weighted reduced identity for that line and every index (`frameNb`). |
| `halfIntegral_iff`, `halfIntegral_iff_local`, `atRep_affine_twice`, `affine_mem_at_odd` | Half-integrality is integrality of ((x+1)/2) in the class order, or equivalently in all its local orders. Twice its local image is (x+1); at odd places its membership is equivalent to membership of (x) (support only). |
| `weightAt_support_iff_affine`, `weight_support_iff_halfIntegral` | The placewise nonzero tests at exceptional primes imply the exact global support equivalence, by the rational intersection, the good-prime test, and the absence of zero divisors (support only). |

## Remaining hypotheses and owners

| Owner | Exact outstanding input |
| --- | --- |
| ELLIOT, discriminant data and (O.3) | Take the manuscript's discriminant and detecting prime. `DisjointDiscriminant` asks that a prime dividing m divide none of 2, N or ℓ₀. Supply `LevelRoots` in the coefficient ring with `ParityAt`: `α_q(-1) = w_{q^e} χ_{h_*}(q)^e`. The construction is parametric in the chosen roots; the existing odd and dyadic existence theorems implement the individual choices. Packaging them in their generated field uses a finite family and a common two-power bound (small). |
| Missing local lattice comparison | Choose `IndexedNeighbourTransport.step` for each line, prove `.class_match` with `nb`, and prove `.lattice`, the equivalence between the neighbour's rational vectors and the `MemNbr p 1` test on px. `Adelic.heckeStep_eq_nbAt` gives the class comparison on an aligned lift. The class representative used by the product may differ there by a local unit: transport that unit in the frame chart or work on the aligned lift and transport the frame back. The matrix test requires matching the integer calculation mod p² to the padic basis-lattice inclusion and using the rational intersection (medium). |
| Same local lattice comparison | `IndexedNeighbourTransport.norm` follows from `levelNormCharacter_single` once the aligned generator is shown to have reduced norm valuation one. Its split determinant is p times an integral unit. No further character theory is needed. |
| This task's support follow-up | `FilteredSupport`: on the specified sphere, with the original level filter, `schwartz h C m hN hne z x ≠ 0 ↔ HalfIntegral (classOrder z) x`. To apply `weight_support_iff_halfIntegral`, prove nonzero iff affine membership at each exceptional prime: unit split norm at level, the affine test and square condition at two, exact norm valuation one at primes of (m), and nonzero residue in the division order from a unit norm (medium). The requested unfiltered proposition `RequestedSupport` is false; it is recorded without assuming it. |
| `rc-pm-geometry` | The actual `PM.Geometry` and `PM.Evaluation` on these ideal classes, with the detector and multiplier (L). The local constructor consumes these only through `pmStage` and `pmValLift`. |

## Known issues

- The late support bridge omits the odd filter used at tex 9122–9135. Take
  `ell₀=3`, `h_*=-7`, and `D=N=193`. Here (D) is squarefree,
  ((D,h_*)=1), ((D/3)=1), and (Dh_*=-1351 = 4(-338)+1 ≡ 1 (mod 8)).
  Moreover `χ_{-7}(193)=1`, so the fixed discriminant itself splits at the level prime.
  In `(-1,-3)`, (x=i+15j+15ij) has trace zero and norm 1351.
  Its affine generator (t=(1+x)/2) is integral in the left order of
  some adelic representative: at 193 use the integral companion lattice
  for (t) and the stable line modulo 193 given by its repeated root;
  at the other split primes use an integral companion lattice when a
  change is needed; at 3 the norm of (t) is the unit 338. Only finitely
  many lattices need to be changed. But at 193 the unit-root weight must
  vanish, since a root of (x) squares to (-1351). Passing to the chosen
  representative of that class conjugates the vector and keeps these
  membership and zero-weight properties. The manuscript's original
  filter excludes this counterexample. This is an arithmetic
  counterexample; the Lean file does not prove the negation of
  `RequestedSupport`.
- In tex 8609–8614, descent on the left is for the coefficient, after
  reindexing the sphere. The weighted product evaluated at the same
  rational vector has the pointwise cancellation on the right only.
- The existing PM audit leaves the scope of the Jetchev–Kane citation
  for arbitrary level prime to the detecting prime, including powers
  of two, UNVERIFIED (`docs/research/rc-pm.md`). The geometric
  identification is out of scope here. No additional printed result
  was invoked.

## Manuscript check

- 8462–8468 — OK: use the explicit order and its existing adelic class equivalence.
- 8494–8498 — gap filled: use a rational intersection to include all the ordinary-place characteristic functions.
- 8499–8515 — OK: transport the existing affine level model and selected cyclic quotient root; the choice with (O.3) is an input.
- 8517–8534 — OK: the dyadic affine test and its scalar factor use the integral projectors of the existing model.
- 8536–8558 — OK: use the existing nilpotent and division factors and their local multiplier rules.
- 8563–8570 — gap filled: definiteness after rational intersection makes each norm sphere finite; integer precision uses the existing coefficient ring.
- 8571–8576 — gap filled: the positive valuation part defines the finite idèle character; on integral order units its factors are exactly the inverse conjugation multipliers.
- 8577–8592 — unverified: the root-number interpretation of the parity of the chosen level characters is an input separate from the local covariance.
- 8594–8604 — OK: on good integers the inverse-idèle convention used in the recurrence is the product of the local scaling factors.
- 8605–8621 — gap filled: left representative change reindexes the rational sphere; right-unit factors cancel in the weighted sum. Mass and precision are provided upstream.
- 9039–9044 — gap filled: actual integral split entries and their reductions mod (p^2) define the frames.
- 9045–9058 — unverified: the line-indexed comparison of the integer test with membership in the actual neighbour lattice remains open.
- 9059–9066 — gap filled: on the corresponding local lattices, multiplication by (p) has the asserted multiplier and gives the finite (y/p)-sum.
- 9067–9076 — gap filled: a one-place step with reduced norm valuation one changes the norm character by the stated Jacobi symbol; the remaining lattice comparison must supply the generator and verify its valuation.
- 9076–9093 — gap filled: the existing stage consumes the exact weighted comparison and the division factor forces vanishing at zero.
- 9122–9135 — unverified: the support comparison still needs the exceptional-place tests under the manuscript's filter. Removing that filter gives the counterexample above.
- 9297–9300 — gap filled: conjugation by a class-order unit becomes an integral right correction, with character one because it is also conjugate to a rational diagonal.
- 9617–9630 — OK: choose the dyadic correction using the sign of the scalar character at minus one times the odd discriminant sign.

The matrix complement, rational intersection and reindexing, positive
rational valuation part, saturation, and vector-level glue are
on-the-spot proofs (provenance (c)) implementing the displayed manuscript
steps. No new printed-form leaves, axioms or imported external sources
are used.

## Verification

Each of the 15 Lean files in `ZInQKernel/Contrib/OneProof/RC/ThetaJoin/`
compiled individually with `lake env lean --threads=1`. The
`#print axioms` audit in `scratch/rc-theta-join/Axioms.lean` covered
all 105 new theorems, including 15 private helpers, and 16 definitions.
Each of the 121 entries reported exactly `propext`, `Classical.choice`,
and `Quot.sound`.
