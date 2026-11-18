# The adelic algebra for Appendix F

The level-N Eichler order inside the explicit maximal order is constructed and
verified. The local-to-global lattice bridge is proved: a full rational lattice is recovered
from its completions, and modifying finitely many completions inside a fixed lattice gives exactly the
prescribed local sublattices. The proofs use coordinate reduction modulo arbitrary
prime powers, so they apply also at the prime two.

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
| `levelOrder_completion`, `levelOrder_le`, `levelOrder_isEichler` | The constructed order lies inside the explicit order, has exactly the prescribed completions, and satisfies `IsEichler ell N`. Supplies rc-eichler item 1 and `Geometry.eichler`. |

## Known issues

The printed locators quoted by the manuscript (Voight Main Theorem 14.6.1 and
Jetchev–Kane §§1.1–1.2, 2.5) are UNVERIFIED here. No manuscript or source error
has been found in the checked steps.

## Manuscript check

| Tex lines | Step | Verdict |
| --- | --- | --- |
| 8464–8465, 8468–8469 | Prescribe level at split primes, including two. | gap filled: the finite lattice patching needed for this construction uses arbitrary prime powers. |
| 8465–8468 | Recover rational lattices from local lattices. | gap filled: coordinate integrality and exact finite patching are proved. |
| 8469–8474 | Identify supersingular pairs and their field of definition. | unverified: this is the geometric comparison. |
