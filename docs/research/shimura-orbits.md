# Shimura's Hecke correspondences on Γ₁(N) orbits

Both Γ₁(N) orbit counts are proved in Lean with multiplicities. The sums
descend to the orbits, and the good-prime correction is the diamond
multiplied by `p`. The two closure laws for `IsXi` now follow from the
analytic point dictionary alone:

```lean
ShimuraSteps.shimuraHeckeRelations_of_pointDictionary :
  ShimuraSteps.PointDictionary → ShimuraSteps.ShimuraHeckeRelations

ShimuraSteps.shimuraThm1Af_of_printed_pointDictionary :
  ShimuraSteps.ShimuraThm1AsPrinted → ShimuraSteps.PointDictionary →
    R16Thm1b.ShimuraThm1Af
```

The Hecke bridge itself is in neither the manuscript nor its
citations. The Shimura paper supplies the rational Hecke ring and its action
on the Jacobian according to the recorded page read; it does not supply the
comparison with these Lean point predicates. No leaf or fold is proposed.

## ON THE SPOT (provenance (c))

For a positive determinant integral matrix whose first column is
`(unit, 0)` modulo the level, take the positive gcd of the first column.
Bézout gives a unimodular left factor, and Euclidean division gives the
reduced offset. The first diagonal entry is prime to the level and the left
factor is in Γ₀(N). Right multiplication by a Γ₀(N) matrix permutes the
triangular forms, by uniqueness of reduction. If the old and new first
diagonal entries are `a` and `a'`, the lower-right entries of the right
multiplier `g` and the reduced left factor `l` satisfy
`a·l₁₁ = g₁₁·a'` modulo `N`. This follows by comparing the first column
and using determinant one for both multipliers. It proves covariance of the
twisted sum under Γ₀(N) and invariance under Γ₁(N). Equal lower-right residues
give the same diamond and the same triangular summand. These arguments take
place on the orbits of the upper half-plane.

For coprime indices, split the product's first diagonal entry by taking its
gcd with each index. If the inner triangle has offset `e` and denominator
`f`, and the outer one has first diagonal entry `a`, offset `b` and
denominator `d`, the composed offset is `a·e + b·f` modulo `d·f`.
Reducing first modulo `f` recovers `e` since `a` is prime to `f`, then
dividing out `f` recovers `b` modulo `d`. This gives a bijection including
every occurrence in each sum.

At a good prime the outer upper branch gives all offsets at denominator
`p·d` by Euclidean division. The outer scaling branch sends the last inner
block (denominator 1) to the last new block. Every other inner block has
denominator `p·d` for some `d`. The scalar `p` can be removed from the
composed matrix in its action on ℍ. The remaining offsets reduce modulo
`d`, each with exactly `p` preimages. The lift still carries the extra
factor `p mod N`, giving the diamond in the correction.

Through `AtTau`, orbit sums of differences map to the tested degree-zero
divisor classes. A triangular correspondence takes a difference of basis
points to a sum of differences with matching representative indices. Thus
the existing formulas for endomorphisms apply after the first correspondence
without requiring a generation theorem for the whole complex Jacobian.
The established pinning and prime formulas then give the existing per-model
assembly.

The orbit argument uses Tau Ceti's Γ₀(N) normalizer and lift facts. Its
Γ₀(N) composite recurrence and character-space actions are independent
calculations; an equality of slash operators would not establish the
multiplicities on Γ₁(N) orbits or retain the diamond here.

## Remaining analytic input

`PointDictionary` quantifies over `N ≥ 2`, `IsCurve X` and
`IsX1Gen N X jX tX` on the given integral rational model and asserts
`∀ τ : ℍ, ∃! x : CPt X, AtTau N jX tX x τ`. It asserts neither a
modular curve construction nor an isomorphism of analytic spaces.
`HeckePin.X1TauPoints` is the existence half. Existence suffices for
pinning. Single valuedness is used at index one and to identify the points
in different occurrences of the same orbit when transporting the counts.

`WeberField.lean` supplies the holomorphic coordinates `Jf`, `Wf` and
their holomorphic polynomial evaluations, with `evAn_eq` on the generic
Weber branch. One must identify the function field with the field generated
by the corresponding meromorphic germs at each parameter. This uses the
identity principle to preserve the algebraic relations and to show that a
nonzero denominator is a nonzero germ. At the exceptional parameters, one
must check that the finite value of the continued quotient gives the
punctured limit in the exact definition of `AtTau`.

Restrict the finite germs to that field. They give a valuation subring and
the value map to ℂ. The given curve is proper and separated; Mathlib has the
valuative criterion in `AlgebraicGeometry/ValuativeCriterion.lean` for the
existence and uniqueness of the lift of this generic point. Evaluating at
the closed end via the value map produces a complex point. The remaining
comparison must identify the stalk image in the function field with the
finite-germ test where needed, and transport its residue evaluation to the
open-section witness in `RegAt`. For uniqueness one must also recover the
same local center and residue map from the one-way implications in
`AtTau`, including the case where the restricted valuation is trivial and
the complex point maps to the generic point of the rational curve.
For the converse comparison, every element of the finite-germ ring is
covered by an integer polynomial quotient, so `AtTau` puts that ring
inside the stalk and agrees with its value map. If a stalk element lay
outside the valuation ring, its inverse would have value zero, contrary
to the stalk element and its inverse both being regular. Thus the inclusion
is equality, which gives the center and evaluation needed for uniqueness.

Mathlib provides analytic and meromorphic orders, stalk maps and the
valuative criteria. It does not provide the comparison of this
two-generator meromorphic field and its finite-value germs with the stalk
and residue evaluation on the given rational model. The needed work is a
substantial local analytic-to-algebraic comparison (several linked lemmas
on germs and on schemes, plausibly several hundred lines). The two main
pieces are the punctured-neighborhood comparison and the stalk/value
comparison. This is local work; full uniformization, cusp compactification
and Abel's theorem are outside its scope.

## Known issues

- The prior recorded page read notes a typo in the conjugate-newform
  sentence before clause (iv) on p. 526: the eigenvalue multiplies the
  conjugate form. That sentence is outside the quotient clauses used here.
- The total Euler identity does not by itself select a constituent at a
  fixed coefficient-field embedding. This audit leaves that selection
  unverified, as it lies outside the quotient bridge.

## Manuscript check

| Lines in `diophantine_zq.tex` | Verdict | Check |
| --- | --- | --- |
| L768–770 | OK | The Li citation supplies the Fricke proviso as recorded in the earlier audit. The correspondence counts do not use it. |
| L770–771 | OK | The recorded page read confirms the quotient construction and total Euler-factor identity under that proviso. |
| L770–773, annihilator images and uniqueness | gap filled | The existing quotient reduction compares the annihilator images and obtains compatible uniqueness using `SameDimFinite`. |
| L770–773, quotient action at every positive index | gap filled | The internal comparison requires the triangular formulas at all positive indices. The orbit counts supply the missing multiplication laws, conditional on the analytic point dictionary for transport. |
| L771–773, fixed Tate constituent and dual | unverified | This run does not verify embedding selection from the total Euler identity or the subsequent representation comparison. |
| L11053–11057 | OK | Bibliography identifies the paper, Theorem 1 and its DOI. |

## Verification

`lake build +ZInQKernel.Contrib.OneProof.ShimuraOrbits` built the five
contribution modules. The [axiom scan](../../scratch/shimura-orbits/Axioms-output.txt)
covers all 47 new theorems and reports only `propext`, `Classical.choice`
and `Quot.sound`.

The stock command ran via `lake env lean scratch/shimura-orbits/DischargesFocused.lean`.
The [full output](../../scratch/shimura-orbits/Discharges-output.txt)
includes the two prior reductions. The two relevant entries are:

```text
DISCHARGES [shimuraThm1Af] by ShimuraSteps.shimuraThm1Af_of_printed'
  still assumes: [ShimuraSteps.ShimuraThm1AsPrinted, ShimuraSteps.ShimuraHeckeRelations]
  axioms: [propext, Classical.choice, Quot.sound]
DISCHARGES [shimuraThm1Af] by ShimuraSteps.shimuraThm1Af_of_printed_pointDictionary
  still assumes: [ShimuraSteps.ShimuraThm1AsPrinted, ShimuraSteps.PointDictionary]
  axioms: [propext, Classical.choice, Quot.sound]
```

## Lean statements

The names below are in `ShimuraSteps.Orbits` unless qualified. Private
helpers are included so the statement list matches the axiom scan.

| Theorem | Statement |
| --- | --- |
| `det_tri` | The determinant of the triangle with diagonal `a,d` is `a*d`. |
| `div_spec` | An eligible `a` and its complementary divisor `n/a` are positive, multiply to `n`, and `a` is coprime to the level. |
| `det_repMat` | The representative matrix has determinant its index. |
| `repMat_repOf` | Repackaging a positive factorization and offset gives the specified triangle. |
| `exists_reduce` | At positive determinant `n), a matrix with first column `(unit,0)` modulo the level factors as a Γ₀(N) element and an eligible reduced triangle. |
| `reduce_unique` | Two reduced triangles at the same index related by left multiplication in SL₂(ℤ) are equal. |
| `matGL_mul`, `matGL_sl` | Passage to real GL₂ preserves multiplication at positive determinant and agrees with the standard inclusion on SL₂(ℤ). |
| `orb_smul`, `orb_eq_of_residue` | Γ₁(N) acts trivially on the orbit set; Γ₀(N) multipliers with the same residue give the same orbit. |
| `diamond_point`, `diamond_independent` | The diamond sends a basis point to its translated orbit and depends only on the lower-right residue. |
| `lift_residue` | The chosen lift of an eligible `a` has lower-right residue `a`. |
| `triAct_eq_smul`, `coe_triAct` | The triangle acts by the real GL₂ action, with complex coordinate `(a*τ+b)/d` at positive diagonal. |
| `triAct_comp`, `triAct_scale` | Triangular actions compose by multiplying matrices, and a positive common scalar acts trivially. |
| `gammaOne_translation`, `orb_triAct_mod` | Integral translations belong to Γ₁(N); reducing the offset modulo its denominator preserves the orbit even after a Γ₀(N) lift. |
| `exists_reduce_right`, `reduce_right_injective` | Reduction after right multiplication gives the residue comparison and injects the finite set of triangles into itself. |
| `triAct_reduce` | The reduction factorization gives equality of actions on ℍ. |
| `term_residue` | A lifted triangular summand depends only on the lift's residue. |
| `sumAt_covariant`, `sumAt_invariant` | The triangular sum is covariant under Γ₀(N) and invariant under Γ₁(N). |
| `R_point`, `sumAt_lifts` | The descended linear map sends a basis point to the sum; any family of lifts with the prescribed residues yields that sum. |
| `diamond_term`, `R_term` | Applying a diamond composes the lifts; applying a triangular correspondence composes the triangles after moving the inner lift out by covariance. |
| `coprime_count_basis` | On every orbit basis point, `R m (R n [τ]) = R (m*n) [τ]` for positive coprime indices. |
| `sumAt_pow`, `sumAt_prime` | At a good prime power, the eligible diagonals are exactly the powers of the prime; at index `p` the blocks are the upper and scaling branches. |
| `prime_block`, `scalar_block` | The upper branch enumerates a full block; a scaled block contributes `p` copies after removing the scalar and reducing its offset. |
| `good_count_basis` | On every orbit basis point, `R p (R (p^(k+1)) [τ]) = R (p^(k+2)) [τ] + p • D_p (R (p^k) [τ])` for a good prime. |
| `orbitPoint_eq`, `clsOrb_point` | The chosen orbit point is the unique `AtTau` point, and the class map sends its basis divisor through Abel–Jacobi. |
| `triAct_eq_shift` | The triangle equals the composite of `mulNat` and `shiftDiv` in `IsXi`. |
| `isXi_iff_compatible`, `compatible_diamond` | The fixed point formula `IsXi` is precisely equivariance on basis differences, and `IsDiamond` provides the corresponding diamond equivariance. |
| `image_R_diff`, `compatible_apply_R_diff` | A triangular image of a basis difference is a sum of paired differences, so equivariance holds after that operation. |
| `isXi_mul_coprime` | The coprime product is closed under the fixed `IsXi` formula. |
| `endA_sub'` | The complex action of abelian variety endomorphisms respects subtraction. |
| `isXi_good_step` | The good-prime recurrence using `IsHeckeT` and `IsDiamond` is closed under the fixed `IsXi` formula. |
| `ShimuraSteps.shimuraHeckeRelations_of_pointDictionary` | `PointDictionary → ShimuraHeckeRelations`. |
| `ShimuraSteps.shimuraThm1Af_of_printed_pointDictionary` | `ShimuraThm1AsPrinted → PointDictionary → R16Thm1b.ShimuraThm1Af`. |
