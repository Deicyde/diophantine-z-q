# The adelic algebra for Appendix F

The ideal class set is identified with the finite adelic double coset set,
and the level-N Eichler order inside the explicit maximal order is constructed
and verified. The two constructions use the same local-to-global lattice
bridge: a full rational lattice is recovered from its completions, and
modifying finitely many full local lattices gives exactly the prescribed
completions. Approximation works modulo arbitrary prime powers, including at
two.

The lattice proofs are on-the-spot (c). No printed-form leaf is added.

## Statements and consumers

Names below are in `ZInQ.Manuscript.RC.Adelic`.

| Declaration | Statement and consumer |
| --- | --- |
| `localCoordinates_toLocal` | The transported basis reads the same coordinates on a rational vector, cast to the local field. |
| `localLattice_basis`, `mem_localLattice_basis` | Completion commutes with spanning an integral lattice on a rational basis; membership is integrality of all local coordinates. |
| `rat_integral_of_local`, `mem_iff_all_local` | A rational number integral at every prime is an integer, and a rational lattice is the intersection of its completions. Both support rc-eichler items 1 and 2. |
| `localLattice_mono`, `localLattice_intersection_le` | Local span is monotone and the completion of the rational intersection is contained in each prescribed lattice. |
| `nat_isUnit`, `finite_prime_dvd` | Away from its finite set of prime divisors, a nonzero natural number is a local unit. |
| `approximate` | The rational lattice maps onto the completed lattice modulo every power of the prime. |
| `patch_inside` | A finite collection of sublattices bounded below by prime-power multiples patches to a full lattice with exactly those completions. This supports rc-eichler item 1. |
| `splitChart_maximal`, `coe_standardOrder` | The chosen splitting takes the maximal order to the full integral matrix ring; the embedded level order is the lower-left congruence set. |
| `standard_smul`, `levelLocal_smul`, `levelLocal_le` | The prescribed local level lattice lies between the maximal lattice and its corresponding prime-power multiple. |
| `levelLocal_mem_split`, `level_patch` | The level condition at a split prime is the pullback of the standard congruence; the local orders therefore patch. |
| `levelOrder_completion`, `levelOrder_le`, `levelOrder_completion_away`, `levelOrder_isEichler` | The constructed order lies inside the explicit order, has exactly the prescribed completions (unchanged away from the level), and satisfies `IsEichler ell N`. Supplies rc-eichler item 1 and `Geometry.eichler`. |
| `isLattice_map`, `localLattice_map`, `localLattice_full` | Linear equivalences preserve full lattices, compatible linear maps commute with completion, and every completion is full. |
| `local_pow_into` | A high enough power of the prime takes any full local lattice into any other. |
| `natScale_apply`, `patch` | Natural-number scaling is the repeated-addition map. Clearing a common denominator reduces arbitrary finite modifications to `patch_inside`. |
| `localUnits_eq_range` | The local subgroup defined by integrality of a unit and its inverse is the image of the completed order's units. |
| `exists_nat_multiple`, `local_le_of_multiple` | A single nonzero natural multiple takes a finitely generated lattice into any full one; the first completion is contained in the second away from that scalar. |
| `finite_localLattice_ne`, `finite_not_mem_completion`, `diagonal_injective` | Full lattices agree almost everywhere, rational quaternions are integral almost everywhere, and the rational units embed diagonally. |
| `mem_localRight`, `localRight_set`, `localRight_eq_iff`, `localRight_one`, `localRight_full` | The translate of the local order is full, and membership is tested by left multiplication by the inverse. Two generators give the same local ideal precisely when they differ on the right by a local order unit. The identity gives the completion of the original order. |
| `adelic_patch`, `mem_fromAdelic`, `fromAdelic_completion` | The intersection of the local right ideals of an adele is a full locally principal right ideal whose completions are exactly the given ones. |
| `exists_adelic_representative` | Every locally principal right ideal comes from an adele; local generators can be taken to be 1 outside a finite set. |
| `fromAdelic_mul_diagonal`, `fromAdelic_translate_iff`, `idealsEquiv_mk` | Rational left multiplication of adeles translates ideals. The fixed-`u` equality of ideals is exactly right multiplication by an everywhere integral unit after diagonal left multiplication by `u`. The equivalence `classesEquiv` evaluates on an adelic representative via this construction. Supplies rc-eichler item 2 and the adelic part of `Geometry.SS` and `classes`. |
| `mem_leftRing_iff`, `fromAdelic_classRepresentative`, `classesEquiv_classRepresentative`, `classGEquiv` | The left ring is the rational intersection of conjugate local orders. The chosen class representative is the same in both models, and `classG` is isomorphic as a group to the units of that intersection. |

## Known issues

The printed locators quoted by the manuscript (Voight Main Theorem 14.6.1 and
Jetchev–Kane §§1.1–1.2, 2.5) are UNVERIFIED here. No manuscript or source error
has been found in the checked steps.

## Manuscript check

| Tex lines | Step | Verdict |
| --- | --- | --- |
| 8464–8465, 8468–8469 | Prescribe level at split primes, including two. | gap filled: the finite lattice patching needed for this construction uses arbitrary prime powers. |
| 8465–8466 | Use the double coset class set. | gap filled: the ideal correspondence and restricted product are constructed. |
| 8467–8468 | Use the units of the adelic left order for automorphisms. | gap filled: the algebraic stabilizer is identified; its geometric interpretation remains outside scope. |
| 8469–8474 | Identify supersingular pairs and their field of definition. | unverified: this is the geometric comparison. |
