# CM field descent sizing and results

Base `60b162a0d`; merged `cb118b8c28` as `33937701f`. Sizing recorded before running Lean. Source checks below are VERIFIED by reading; proposals are on the spot (c).

| Step | Available and missing |
| --- | --- |
| 1a: integrality | Vendored `eval_jLattice_eq_zero_of_isAddCyclic` and `isUnit_leadingCoeff_diag_of_not_isSquare` take a genuine cyclic sublattice and give the diagonal equation and a unit leading coefficient. Normalizing it is small. Remaining lattice work: period basis of an embedded fractional ideal, homothety invariance, primitive multiplier gives cyclic quotient and its index is the positive norm, and choose a nonsquare norm. |
| 1b: multiplicities | Root membership, monicity and degree do **not** imply the asserted product at a repeated-root specialization. The vendored formal `eq_cosetTwoVarPoly_of_forall_isRoot` uses distinct Laurent series; the analytic product can instead use pairwise distinct translates near the cusp then analytic continuation. The merged `orbitPoly` has the corresponding SL₂ coset degree and analytic coefficients; identifying this product with the primitive triangular coset reps needs the orbit/coset dictionary. |
| 1b: exact order and Pic | `jLattice_surjective` gives a complex period pair; the existing cyclic-sublattice theorem goes from sublattices to roots, not from roots to sublattices. Tau Ceti already defines `Pic O` as invertible fractional ideals modulo principal ideals; `mkPic` is onto and Mathlib's class group API characterizes equal representatives. Fowler's `proper_iff_isUnit` on fork main supplies the proper-to-invertible direction for quadratic orders, after passage to a fractional ideal. An arbitrary period lattice still needs rescaling into the embedded quadratic field, and identifying its **exact** multiplier order under conjugacy. The imported degree print would bypass the step and is excluded. |
| 2: ring class field | `ringClassArtinEquiv` describes arithmetic Frobenius on the class field. `GlobalExistence/NormLimitation.lean` and `Correspondence.lean` give norm subgroup comparisons for finite abelian layers. Chebotarev supplies primes in a prescribed conjugacy class; split-prime inclusion can be proved by applying it to a finite Galois compositum. Neither identifies the analytic class invariants. `KroneckerCongruence` is an unproved polynomial identity over ZMod ℓ (no CM theory in its statement); getting the correct oriented Frobenius on singular moduli additionally needs integral reduction and a way to choose the correct factor. Closure of the j-set under conjugacy does not alone prove the action consists of Picard translations. |
| 2: Heegner coordinates | The paper calculation uses `(A,B,C) ↦ (A/N,B,NC)` with the same primitive discriminant, and the product of the two-generated ideals. Need the bridge from these embedded lattices to invertible ideals in the given abstract order. |
| 3: branch | `finitePointEval` and affine chart injectivity support descent of the evaluation map by range restriction. Level one has just the j-coordinate (need compare its normal model to the j-line). The denominator in `exists_analyticJN_ratio` represents j_N by chart sections, i.e. in the opposite direction from expressing all chart sections in the two coordinates. Its nonvanishing alone is not a descent criterion; a local presentation of the normalization over the plane pair would suffice. Level two provides a diagnostic collision. |
| Integration | `CMFieldOfDefinition` does not appear in `docs/one-proof/kinds.tsv` or `docs/one-proof/OPEN.md` at the merge. No discharge count, spec, or autofold dry run applies. |

- VERIFIED (source): Tau Ceti supplies the split-prime criterion
  `ncard_primesOver_ringClassField_eq_finrank_iff`. For inclusion only, it suffices
  to compare Frobenius at rational primes that split in the quadratic field and
  whose primes there split completely in the ring class field. This asks for the
  diagonal Kronecker congruence and excludes a finite set of primes separating
  conjugates. No selection of an oriented congruence factor is needed.
- SPECULATIVE (formal roadmap): count cyclic self-isogenies at the least nontrivial
  cyclic degree to recover the trace parity of the multiplier order. This uses
  the analytic product with multiplicities, the inverse index-to-lattice
  dictionary, and a separate argument for the two orders with extra units.
- VERIFIED (build): the first serialized import build reached the normalized
  curve's affine and overlap modules. Several queued imports were stopped by
  the load guard (exit 77); the run was held while the one-minute load was
  above 150. Previously built objects remain available for the resumption.
- VERIFIED (Lean): `Frobenius.lean` compiled using `lake env lean`. In a
  field the diagonal Kronecker factors force `x ^ p = x`; separating
  reductions for each automorphism of the overfield fixing the proposed
  subfield imply membership by Galois correspondence. Both theorems use
  only `propext`, `Classical.choice` and `Quot.sound`.
- VERIFIED (Lean): `Diagonal.lean` compiles with the three standard axioms.
  Diagonal evaluation specializes both slots; embeddings preserve the
  multiplicity of the diagonal root. A cyclic self-isogeny of nonsquare
  degree gives a monic integral equation, and every quadratic norm
  polynomial of negative discriminant has a value between consecutive
  positive integer squares.
### Lattices and cyclic quotients

VERIFIED with the guarded local Lean check: `Lattices.lean` constructs period pairs from invertible fractional ideals, proves scale invariance, and shows that the singular modulus depends only on the Picard class. `Cyclic.lean` proves the rank-two primitive sublattice quotient criterion by Smith normal form. Each new theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.

### Kronecker congruence

VERIFIED (Lean): `Kronecker.lean` proves `kroneckerCongruence_of_prime` for the existing vendored definition, and `pow_eq_of_modularPolynomial_diagonal_root` for any characteristic-`p` residue field. It reduces the integral Laurent-series relation, applies characteristic-`p` Frobenius and transcendence, then uses symmetry, monicity and degree to identify the entire polynomial. All axiom checks returned only `propext`, `Classical.choice`, and `Quot.sound`.

### Specialized coset product

VERIFIED (Lean): `Factorization.lean` proves the product with multiplicities at every analytic specialization. For transcendental parameters, coincident translates would give a nonzero quadratic relation over ℚ; the vanishing coefficient case forces the two triangular representatives to agree. The monic degree count at such parameters is extended by density and continuity. `CosetLattice.lean` constructs a cyclic sublattice for each specialized root, proves surjectivity of analytic j, and transfers a detected cyclic self-isogeny degree to every embedded conjugate. All declarations checked with the three standard axioms.

### Algebraic integrality

VERIFIED (Lean): `Integrality.lean` proves `singularModulus_isIntegral` for every proper invertible ideal in an imaginary quadratic order. The integer index of a scaled sublattice equals the real determinant of multiplication, i.e. squared complex norm. The basis `[1,ω]` and invertibility show that a scalar `n+ω` is primitive in the ideal's multiplier ring. The nonsquare norm lemma and the cyclic quotient criterion then give the monic equation. The same file verifies the norm identity for principal integral ideals and the prime-level diagonal equation for any order multiplier of prime norm. The axiom checks returned only `propext`, `Classical.choice`, and `Quot.sound`.

### Degree and exact order

VERIFIED (Lean): `Degree.lean` proves the bound over ℚ and through κ over the quadratic field from `ConjugateSingularModulus`. This uses the existing finite `Pic O`, representative independence, and the count of embeddings, independently of the degree print on fork main. `IdealDictionary.lean` ports the proper-to-invertible implication and proves that a complex period lattice whose multiplier order is exactly κ(O) yields one of these singular moduli. `ExactOrder.lean` uses the preservation of diagonal multiplicities under embeddings and the dictionary to derive `ConjugateSingularModulus` from `ExactMultiplierOrderOfDiagonalMultiplicities`. The comparison asks only which order the conjugate period lattice has and is proved in `ExactOrderProof.lean`. Axiom checks on all three files returned the three standard axioms.

VERIFIED (Lean): `ScalarWitness.lean` makes the self-isogeny witness a scalar. Equal j-values give homothetic lattices; a real multiplier of a complex period lattice is an integer, and its index is a square. Thus each conjugate detected at a nonsquare level has a nonreal multiplier. `OrderGenerator.lean` computes the discriminant in an order basis starting with 1 and constructs an oriented generator with the specified complex image for a form of that discriminant. Both files compile with the three standard axioms.

VERIFIED (Lean): `Cyclic.lean` now proves both directions of primitivity for a rank-two sublattice. `Multipliers.lean` constructs a basis of the embedded multiplier ring with generator of normalized integral trace and norm. `NormCriterion.lean` identifies support of the specialized diagonal modular polynomials at levels above one with the primitive norm support. `PrimitiveNorms.lean` determines the normalized trace and norm from that support, with finite residue calculations also handling Gaussian and Eisenstein orders. `ExactOrderProof.lean` closes `ExactMultiplierOrderOfDiagonalMultiplicities` and `ConjugateSingularModulus`; the final `singularModulus_finrank_le` and `singularModulus_finrank_over_base_le` have no comparison hypotheses. Each listed file was checked with the three standard axioms (or a subset). The import build of the branch and class-field layers was paused with cached outputs while checking these independent files and resumed afterward.

### Ring class field comparison at split primes

VERIFIED (Lean): `Membership.lean` states the simultaneous comparison in a single embedding extending the fixed embedding of the quadratic field. `SplitPrime.lean` proves that at a conductor-coprime prime of norm `p` splitting completely in the ring class field, every integral lift of a proper ideal singular modulus reduces to a root of `X^p − X`. This uses the principal generator furnished by Tau Ceti and the diagonal of the specialized modular polynomial. `MembershipDegree.lean` also derives the degree bound over the quadratic field from membership alone. All three checks used only the standard axioms. The remaining import build used local cached artifacts after confirming identical transitive source files and matching package versions.

### Affine descent and level one

VERIFIED (Lean): `Descent.lean` states `BranchDescends N`, descends a field point by restricting the affine evaluation homomorphism to the image field, and gives the conditional all-level `cmFieldOfDefinition_of`. Local criteria use either containment in the field generated by the two coordinates or explicit rational expressions for the normalized sections with nonzero evaluated denominators. `LevelOne.lean` proves that evaluation of the pulled back j-line chart is ordinary polynomial evaluation, that the pullback is surjective at level one, and that a fixed finite family of module generators suffices for the range test at all levels once the first coordinate lies in the field. Lake completed the build of the required import targets; both files checked with only the three standard axioms.

### Heegner lattice calculation

VERIFIED (Lean): `OrderGenerator.lean` chooses the sign of the order generator in an arbitrary prescribed complex embedding. `HeegnerLattice.lean` proves the scaled primitive form identity, the product of the two generated lattices `(N, ω)(A/N, ω) = (A, ω)`, and the `cmPoint` dilation formula. Both compiled; each axiom check returned a subset of the three standard axioms.

### Ring class membership

VERIFIED (Lean): `PrimeComparison.lean` proves `singularModulusMemRingClass`. Chebotarev is applied inside a finite normal closure over ℚ, with a bound excluding both the conductor and the norm of a nonzero difference of conjugates. The Frobenius restriction forces prime residue degree one in the two embedded fields, and trivial inertia gives complete splitting over the quadratic field. The split-prime diagonal equation then contradicts a nonzero difference for an automorphism fixing the ring class field. The proof works for every proper ideal in a single embedding of the ring class field extending the chosen quadratic embedding. All six axiom checks returned subsets of the three standard axioms.

VERIFIED (Lean): `OrientedIdeals.lean` identifies the additive lattices with invertible proper fractional ideals in the prescribed order. The scaled ideal is the inverse translate by the oriented level ideal. `CoordinateDescent.lean` proves `BranchDescends 1`, and `Results.lean` proves the field-of-definition statement unconditionally for both level-one models, and at general level from `BranchDescends N` alone. It also puts both plane coordinates in one embedding of the ring class field, without comparison hypotheses. All three files checked with the standard axioms.

VERIFIED (Lean): `LevelTwo.lean` checks the two forms at discriminant −7, coprimality, equality of both plane coordinates, distinct points on the normalization, the middle-coefficient invariant modulo four, and the reflection identity for the parameters. The axiom checks used subsets of the three standard axioms.

VERIFIED (Lean): `AnalyticDegree.lean` also proves the upper degree bound when the singular modulus is specified by a primitive analytic period equation, the input shape of the fork's degree print. `fieldPoint_iff_finitePointEval_range` checks that the branch condition is both necessary and sufficient for descent over a fixed embedded field. Both checked with the standard axioms.

### Final validation

VERIFIED (Lean): The serialized `lake env lean` checks of all 29 new modules completed with exit code 0 and no diagnostics. `Check.lean` also passed; `statements.txt` records the public theorem types and comparison definitions. `axioms.txt` records 153 checks (142 theorems and 11 definitions), all subsets of `propext`, `Classical.choice` and `Quot.sound`. The transitive project import audit found neither a prohibited import path nor an import of the headline entry point. The integration row search at `33937701f` returned no matches.
