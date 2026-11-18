# The adelic algebra for Appendix F

The level-N Eichler order in the explicit quaternion algebra, its adelic
class set and left-order unit groups, and the adelic Atkin–Lehner,
division-uniformizer, and good-prime Hecke operations are proved. The Hecke
action matches the existing ideal neighbours line by line and preserves the
multiplicities when several lines give the same class. `algebraicGeometry`
assembles the algebraic inputs to RC/PM for prime `ell ≡ 3 mod 4` and positive
`N` coprime to `ell`.

The two global constructions use the same lattice bridge: a full rational
lattice is recovered from its completions, and a finite change of full local
lattices gives exactly the prescribed completions. The approximation works
modulo arbitrary prime powers, including at two. The lattice gluing, quotient
descent, and matrix and ideal comparisons are on-the-spot (c). No printed-form
leaf is added.

All eleven new Lean files were checked individually with
`lake env lean --threads=1`. The `#print axioms` checks list only
`propext`, `Classical.choice`, and `Quot.sound` or a subset of those.

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
| `fromAdelic_mul_diagonal`, `fromAdelic_translate_iff`, `idealsEquiv_mk` | Rational left multiplication of adeles translates ideals. The fixed-`u` equality of ideals is exactly right multiplication by an everywhere integral unit after diagonal left multiplication by `u`. The inverse equivalence `idealsEquiv` sends an adelic representative to the class of its ideal. Supplies rc-eichler item 2 and the adelic part of `Geometry.SS` and `classes`. |
| `mem_leftRing_iff`, `fromAdelic_classRepresentative`, `classesEquiv_classRepresentative`, `classGEquiv` | The left ring is the rational intersection of conjugate local orders. The chosen class representative is the same in both models, and `classG` is isomorphic as a group to the units of that intersection. |
| `single_same`, `single_away` | A one-place adele has the specified component there and identity elsewhere. |
| `localUnits_conj`, `normalizes_single`, `normalizes_inv`, `right_respects` | A local normalizer preserves the order unit group under conjugation, hence the one-place adele normalizes the everywhere integral group. The inverse also normalizes, and right multiplication respects the double coset relation. |
| `rightPerm_mk`, `rightClassPerm_mk`, `rightClassPerm_involutive` | The descended permutation is right multiplication on representatives in either model. If the square is a central rational unit times an integral adele, the class permutation is involutive. |
| `atkinMatrix_square`, `atkinMatrix_conj_formula`, `atkinMatrix_conj`, `atkinLocal_conj` | The matrix with off-diagonal entries 1 and `p^e` squares to `p^e`. Its inverse conjugation sends the entries `(a,b;c,d)` to `(d,c/p^e;p^e b,a)`, preserving the standard order and its pullback. |
| `split_of_factorization_pos`, `diagonal_scalar_val`, `atkin_involutive` | A level prime is split because the level is coprime to the discriminant. The rational scalar has its usual value at each prime. The square of the one-place operator differs from the diagonal scalar by local units everywhere. Supplies `Geometry.atkin` and `atkin_involutive`. |
| `level_completion_division`, `divisionUnit_normalizes`, `uniformizer` | The level order has the same completion at the ramified prime as the explicit order. The given division uniformizer `j` normalizes it, and its one-place right action is a permutation. Supplies `Geometry.uniformizer`. |
| `matrix_on_line`, `basis_in_hecke_double`, `basis_right_distinct`, `hecke_matrix_cosets` | A residue matrix of determinant zero has its columns in a line. Every line basis is in the double coset of `diag(p,1)` and the line bases are pairwise inequivalent on the right by integral units. Every element of the double coset has a unique such right coset. |
| `heckeBasis_val`, `localUnits_split`, `heckeLocal_cosets`, `heckeBasis_mem_double` | The chosen good-prime splitting transports the matrix representatives and the integral matrix units into the local algebra. The double coset and its right cosets are the same in the two presentations. |
| `heckeAtRep_eq_of_rel`, `hecke_mk` | Changing an adelic lift permutes the right coset terms, and the quotient operation evaluates by their multiset on any lift. |
| `exists_aligned`, `aligned_ideal`, `aligned_gen` | A lift of the chosen ideal representative can be chosen with the generator used by the ideal's matrix chart; the adjustment is by a local order unit. |
| `heckeStep_eq_nbAt`, `heckeStep_eq_neighbours`, `hecke_eq_neighbours` | The adelic step gives the same ideal kernel at each line, hence the same total neighbour map at a good prime and the same multiset of classes. This supplies the algebraic correspondence used in `Geometry.hecke`; the equality of specialized points is still geometric. |
| `finite_doubleCosets` | The adelic class set is finite by the existing ideal class finiteness theorem for definite orders. |
| `algebraicGeometry` | Assembles `ram` from explicit ramification, `eichler`, `classes : ClassSet R ≃ DoubleCosets R`, `atkin`, `atkin_involutive`, and `uniformizer` for the explicit level order. |

## RC/PM handoff

Compose `algebraicGeometry.classes` with the geometric identification of the
adelic set with supersingular pairs for `Geometry.SS` and `Geometry.classes`.
The following fields still require modular or geometric inputs:
`specialize`, the specialized eigenidentity `hecke`, `atkinSign`,
`atkinSign_eq`, `cusp`, `atkin_affine`, `frobSS`, `uniformizer_spec`, and
`specialize_frob`. In particular the algebraic right action of `j` does not
supply its geometric identification with Frobenius. The torsion and Heegner
specialization identities and the construction of `P_M` remain with their
respective tasks.

## Known issues

The printed locators quoted by the manuscript (Voight Main Theorem 14.6.1 and
Jetchev–Kane §§1.1–1.2, 2.5) are UNVERIFIED here. No manuscript or source error
has been found in the checked steps. The Eichler order statement uses the
tree's definition by local normal forms. The finite adelic group here has its
restricted product description as a group and does not require topology.

## Manuscript check

| Tex lines | Step | Verdict |
| --- | --- | --- |
| 8462–8463 | Choose a quaternion algebra ramified exactly at the detecting prime and infinity. | OK: the imported explicit ramification theorem verifies this presentation. |
| 8464–8465, 8468–8469 | Prescribe level at split primes, including two. | gap filled: the finite lattice patching needed for this construction uses arbitrary prime powers. |
| 8465–8466 | Use the double coset class set. | gap filled: the ideal correspondence and restricted product are constructed. |
| 8467–8468 | Use the units of the adelic left order for automorphisms. | gap filled: the algebraic stabilizer is identified; its geometric interpretation remains outside scope. |
| 8469–8474 | Identify supersingular pairs and their field of definition. | unverified: this is the geometric comparison. |
| 8476–8479 | Specialize the modular parametrization at the detecting prime. | unverified: the specialization of the map is outside scope. |
| 8480–8484, 9040–9042 | Use the good-prime Hecke correspondence with its p+1 line terms. | gap filled: the local double coset gives precisely the existing ideal neighbours, with multiplicity. |
| 8484–8487 | Intertwine Hecke with the eigenvalue after specialization. | unverified: the eigenidentity for the parametrization is geometric. |
| 8487–8489, 9331–9338 | Act by the one-place Atkin–Lehner normalizer. | gap filled: normalization, descent, and the removal of the square by a rational scalar and order units are proved. |
| 8488–8489, 9334–9339 | Use the Atkin–Lehner eigenvalue and fixed cuspidal translation. | unverified: this parametrization identity is outside scope. |
| 8489–8490, 9343–9346 | Act on classes by the right division uniformizer. | OK: the imported local model supplies j and its norm; its right action descends to a permutation. |
| 8489–8490, 9347–9358 | Identify this action with Frobenius on pairs and specialize equivariantly. | unverified: the correspondence with Frobenius and the specialization are geometric. |
