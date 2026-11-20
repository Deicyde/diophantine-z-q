**Main result.** `ThetaClose.actualPmLocal` inhabits
`PMLocal (Coefficients hN H w) (levelRing h hN) M N ell` for the
explicit level order and the discriminant and Atkin–Lehner data
listed below. It proves all three fields of the indexed neighbour
transport and builds the level characters in the valuation ring
of their field of values. The only frame change is the integral
unit required to transport the chosen generator. The stage and
valuation lift call `pmStage` and `pmValLift` on this actual local
datum. No new printed leaves are used.

`ThetaClose.actualFilteredSupport` supplies the filtered sphere
support equivalence for the same Schwartz function, independently
of the stage geometry. Consumers can use the equivalence at a
chosen index with `RequestedIndices` and `LevelFilter`.

## Known issues

- The inherited Lean `FilteredSupport` lacks parentheses around the support
  equivalence. Lean parses its innermost conclusion as
  `(traceZero → normOnSphere → nonzero) ↔ HalfIntegral`.
  The manuscript asserts `traceZero → normOnSphere → (nonzero ↔ HalfIntegral)`.
  This change states the latter explicitly and leaves the inherited file intact.
  `RequestedSupport` has the same parsing problem; the join report's
  counterexample also rules out its intended sphere-restricted version.

- The inherited `levelFrameCoordinates` uses the chosen adelic representative
  but the line labels in `LineIndex.chartAt` use its separately chosen local
  generator. Their ratio is an integral unit and can permute the residue lines.
  The formulas need the chart transported by this ratio. The stage and lattice
  comparisons must share the transported chart. The original convenience
  wrappers `levelPmLocal`, `levelStage`, and `levelValLift` fix their
  frame by definition. The new wrappers call the same constructors with
  `alignedFrame`, retaining the original Schwartz function, adelic
  representative, and line indices.
- The unfiltered `RequestedSupport` remains false. The join report gives
  `D = N = 193`, `h_* = −7`, and `ℓ₀ = 3`: the affine generator can be
  integral but the local norm at 193 is not a unit. The manuscript's
  level filter excludes that example. The negation is recorded here
  as an arithmetic counterexample; it is not a new Lean theorem.
- For tex 8609–8614, the inherited join treats descent on the left as
  descent of the coefficient after reindexing the norm sphere. The
  new assembly reuses that descent in `weightedNeighbour_of_transport`.

## Formal statements

The declarations are in `ZInQ.Manuscript.RC.ThetaClose`. A line `L`
uses the column matrix `B_L` from `LineIndex.basisMatrix`. Write
`v_z` for `classRepresentative z` and `g_(p,z)` for the local
generator in `LineIndex.chartAt`.

| Declaration | Statement and use |
| --- | --- |
| `integerBasis_det`, `integerBasis_cast`, `integerBasis_image` | The integer lift of `B_L` has determinant p, casts to `B_L`, and its image is the set of integer vectors satisfying `InL p L`. |
| `integer_test`, `basis_test` | `MemNbr p 1` holds iff `Y B_L = p B_L T` for an integer matrix T. Over either integral domain this equation is solvable iff p² divides every entry of `adj(B_L) Y B_L`. |
| `memNbr_iff_padic_basis`, `coord_memNbr_iff` | Reduction of the entries modulo p² transfers the test to the p-adic basis equation. The three residues in `FrameCoordinates.coord` suffice since the matrix has trace zero. |
| `conjugateChart_mem`, `at_step`, `local_step_iff` | Conjugating by the correction preserves the completed order. At the step prime the new representative acts by conjugation by the step, and new-order membership is `X B_L = B_L T` in the transported chart. |
| `scale_p_away_iff`, `transportedNeighbourLattice` | Away from p, scaling by p preserves membership. Rational intersection gives the equivalence of membership in the stepped left order with px in the original ternary lattice and satisfying its indexed `MemNbr p 1` test. Supplies `lattice`. |
| `indexedStep_class` | The local step `v_(z,p)⁻¹ g_(p,z) heckeBasis(L)` gives the same right ideal as the step on the aligned lift, whose class is `nbAt` by `heckeStep_eq_nbAt`. Supplies `class_match`. |
| `heckeBasis_norm`, `indexedStep_valuation` | The basis has reduced norm p; the correction has norm valuation zero. The step has valuation one. `levelNormCharacter_single` supplies `norm`. |
| `prime_not_dvd_of_symbol_ne_zero`, `discriminantDisjoint`, `levelCoprime` | A nonzero prime Jacobi symbol excludes divisibility of the numerator. The primes of m avoid 2, N and ℓ₀ by the fixed odd discriminant and level/detecting-prime conditions. Supplies `DisjointDiscriminant` and coprimality for the level characters. |
| `prescribedParity_val`, `complexCharacter`, `chosen`, `mem_boundPrimes`, `complexRoots_parity` | The target integer unit is `w_(q^e) χ_(h_*)(q)^e`. The odd and dyadic existence results give a character with that parity at each prime. The finite indexing set consists of exactly the primes of N, and the supremum of the individual exponents gives a common bound. |
| `characterValues_order`, `coefficientPlace_over_two`, `liftCharacter`, `levelRoots_parity` | All values are killed by the common two-power; their generated field is a number field, the chosen place lies over two, and each character lifts with the same values. The resulting `LevelRoots` satisfy `ParityAt` in the coefficient ring. |
| `extend_nonzero`, `affine_range` | A function extended by zero is nonzero exactly on the image of input points with nonzero weight. The trace-one affine image in the chart is equivalent to membership of `(1+x)/2` in the local order. |
| `affine_det`, `affine_det_on_sphere`, `positive_level_split` | `det(2Y−1) = 4 det Y−1` for `tr Y = 1`; if `Dh_* = 4k+1`, the affine determinant is −k. At positive level the residue root is simple when the discriminant is a unit. |
| `levelSupport`, `dyadicSupport`, `nilSupport`, `divisionSupport` | The four local factors are nonzero exactly when the affine generator is integral on the indicated sphere. The tests are unit discriminant, even affine determinant, valuation-one norm, and unit division norm respectively. |
| `filteredSupport`, `actualFilteredSupport` | `weight_support_iff_halfIntegral` on the original filtered sphere, first for any integral coefficient domain and level characters, then for the actual chosen coefficient ring and characters. |
| `exceptionalProduct_ne_zero` | The exceptional-prime indexing product `2mNℓ₀` is nonzero, by positivity. |
| `indexedTransport`, `actualPmLocal` | The actual level norm character and the transported coordinates satisfy `IndexedNeighbourTransport`; with disjointness these give the explicit `PMLocal`. |
| `actualLevelStage`, `actualLevelValLift` | The stage and its integral valuation lift on the same local datum, conditional on the existing `PM.Geometry`, `PM.Evaluation`, and multiplier. |

The matrix divisibility, coordinate transport, rational intersection,
finite family packaging and exceptional support comparisons are
on-the-spot proofs (provenance (c)). The local roots, conjugation and
weight laws reuse the existing modules. No new printed leaves or
references are used.

## Manuscript check

- 2404–2409, 8210–8213 — OK: the negative fixed discriminant and eligible positive indices have the specified odd unit classes at 2N.
- 8432–8438 — OK: use the detecting prime with ℓ₀ ≡ 3 mod 4 and the fixed discriminant inert there.
- 8494–8515 — gap filled: use the affine integral chart and the simple residue root at odd level; choose the stipulated parity from the cyclic character.
- 8517–8534 — gap filled: the even affine determinant detects the split condition at two; positive dyadic level uses the selected residue root and the character modulo four.
- 8536–8558 — gap filled: the sphere gives valuation one at the primes of m and a unit norm, hence nonzero residue, at ℓ₀.
- 8563–8577 — gap filled: choose a place over two of the field generated by the finite family of chosen values, with one two-power bound for that family.
- 8577–8592 — unverified: this construction uses the Atkin–Lehner signs as inputs and does not use the root-number interpretation of their product.
- 9039–9058 — gap filled: identify the completed basis of each indexed line, transporting the local generator before comparing the integer test modulo p².
- 9059–9066 — OK: use the join's per-line scaling identity on the proved rational lattice bijection.
- 9067–9076 — gap filled: the norm valuation of the specific indexed step is one, so the character changes by the stated symbol.
- 9076–9093 — OK: use the existing stage recurrence with the transported frame and its actual weighted neighbour law.
- 9105–9108, 9119–9135 — gap filled: apply rational intersection to the exceptional support tests under the stated filter. The subsequent orbit comparison is outside this change.

## Remaining hypotheses and owners

| Boundary | Exact inputs | Owner |
| --- | --- | --- |
| Local construction | Positive N; prime ℓ₀ ≡ 3 mod 4 with gcd(N, ℓ₀) = 1; h_* = −m with m squarefree, m ≡ 3 mod 4, h_* ≡ 1 mod 8, (h_*/q) = 1 for each odd prime q dividing N, and (h_*/ℓ₀) = −1; integer units w(q) giving the Atkin–Lehner signs at q to its exact exponent in N. Precision M is a parameter. | Upstream discriminant and detector data; the fixed curve supplies the Atkin–Lehner signs. |
| Support instance | Positive squarefree D, gcd(D,m) = gcd(D,N) = 1, (D/ℓ₀) = 1, Dh_* = 4k+1 ≡ 1 mod 8, and (Dh_*/q) = 1 for each odd prime q dividing N. These are the existing `RequestedIndices` and `LevelFilter`. The vector has trace zero and norm mD. | The fixed odd filter and the chosen index and vector. |
| Stage and valuation lift | `G : PM.Geometry K (levelRing h hN) N Ebar ap`, `d : PM.Evaluation K Ebar M`, and the multiplier `L : ℕ`. The standard field and elliptic curve instances are parameters as in the existing stage. | PM geometry/evaluation handoff and upstream detector/multiplier. |
| Support consumers | Orbit exhaustion, character constancy, and the resulting comparison in (O.7). None is a parameter of the local data or the support theorem. | O.7 follow-up tasks. |

## Verification

All five new Lean files compiled individually with
`lake env lean --threads=1`. The separate `#print axioms` check in
`scratch/rc-theta-close/Axioms.lean` passed for all 39 theorems,
including private helpers, and 24 other declarations.
Every theorem, including the support and stage results, uses exactly
`propext`, `Classical.choice`, and `Quot.sound`. The only exceptions
among the other declarations are `integerBasis` and `ternaryMatrix`,
which use `propext` and `Quot.sound`. There are no new axioms or
placeholders.
