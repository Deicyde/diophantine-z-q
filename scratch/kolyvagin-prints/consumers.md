# Kolyvagin consumers at the pinned base

**VERIFIED (Lean source).** Paths in the table start at
`ZInQKernel/Contrib/`. `E^a` denotes the actual `qtwist E a`;
`Etw ℓ a` is the twist of the fixed family member `Ecurve ℓ`.
Each direct call has ellipticity and invokes BCDT for its modularity.
`r0` means `AnalyticRank _ 0` (nonzero central value of an entire
continuation), and `r1` means `AnalyticRank _ 1` (a simple zero).
“Finite Sha” in the table describes the argument actually passed to the
current downstream interface, even when the conclusion itself only needs
information at two.

| Direct theorem or adapter | Curve and analytic input | Weakest projection used |
| --- | --- | --- |
| `CloudB3RC53/GenusOdd/Artin34.lean:202,206,216`, `core34'` | `E^h` at r1 from `hz`; `E^hstar` at r0 from `GenusPartner`; `E^(h*k')` at r0 from `Companion`. `E` is an arbitrary elliptic curve with the stated normal-model and non-CM lattice data. | Rank at most 1 for `E^h`, to make two points dependent in `rank_one_ratio`; rank 0 for the other two (all rational points torsion). No Sha. |
| `CloudB3RC53/GenusOdd/GenusLower.lean:367,371,381`, `core34` | Same three twists and analytic inputs as `core34'`. | Same projections. |
| `CloudB3RC53/GenusOdd/Witness.lean:68`, `fixedWitness_proof` | `E^hstar`, r0 from `GenusPartner`; arbitrary elliptic base curve with the normal-model and non-CM lattice data. | Rank 0, used to get all rational points torsion. No Sha. |
| `OneProof/RC/GlueSweep/AnaForward.lean:37`, `forwardRank_zero_of_prints` | Any elliptic `E/ℚ` with r0. | Rank 0 and finite Sha, via the Kummer corank-zero theorem. Its downstream uses include the rough companion and the even locus. |
| `OneProof/RC/GlueSweep/OddGenusTorsion.lean:98`, `genusIndex_eq_top_of_not_simpleZero` | `E^hstar`, r0 from `GenusPartner`; arbitrary elliptic base curve with the normal-model and non-CM lattice data. | Rank 0, used to get all rational points torsion. No Sha. |
| `OneProof/RC/Skeleton/Skeleton.lean:141`, `selmerCorankOneOverK_of` | `Etw ℓ k` at r0, with `0 < ℓ` and `k ≠ 0`. The original curve's corank is an input. | Rank 0 and finite Sha for the companion. |
| `OneProof/RC/Stages/ExactGenus.lean:169`, `exact_twist_of_genusPoint` | `(C⁄ℚ)^hstar` at r0 from `GenusPartner`, for integral model `C` elliptic over ℚ with `a₁ = a₃ = 0`. | Rank 0, used to get all rational points torsion. No Sha. |
| `OneProof/RC/Wiring/CalibrationPrints.lean:332,335`, `CalibrationModelP.nonempty_modelR` | `Etw ℓ (Fam.h x)` at r1; `Etw ℓ (Fam.h x * D.kfin)` at r0. The nonzero twists come from the address and its fixed companion. | Exact ranks 1 and 0 for the free generator and the rational 2-primary index calculation. No Sha. |
| `OneProof/RC/Wiring/Genus.lean:76`, `forward_corankZero` | `Etw ℓ d` at r0, with `0 < ℓ` and `d ≠ 0`. | Rank 0 and finite Sha for the Kummer corank-zero conclusion. |
| `OneProof/RC/Wiring/SignedCalibrationLeaf.lean:204–205`, `selmerCorankOneOverKSigned_of_forward` | `Etw ℓ h` at r1 and `Etw ℓ (h*k)` at r0, for `(ℓ : ℚ)*h ≠ 0` and `k ≠ 0`. | Exact ranks 1 and 0 and finite Sha on both; handed to the rank-one and rank-zero Kummer corank arguments. |
| `RC53Assist/EvenUpper/Faithful.lean:296`, `forward_of_analytic_leaves` | `Etw ℓ d` with `0 < ℓ`, `d ≠ 0` and nonzero normalized central value, converted to r0 by `LstarTarget`. | Rank 0 and finite Sha for the Kummer corank-zero conclusion. |
| `RC53Assist/EvenUpper/Faithful.lean:307`, `forward_of_weil_leaves` | Same as the preceding row. Takes the weak-Weil variant and its BCDT-to-parametrization bridge. | Same rank-zero projection via the conditional adapter. |

The first ten rows read `Prints.kolyvagin` directly (16 projection calls
in ten theorems). The last two take the theorem Prop expressly. For a
consumer that concludes only a Selmer corank, finiteness of the 2-primary
part would suffice mathematically; equivalently, in the usual Kummer rank
formula only its corank enters. The existing Kummer calls accept finite
full Sha.

The remaining executable uses of the weak-Weil statement are adapters:
`Prints/Kolyvagin.lean:93,100` under `CloudB3RC53/` forwards both ranks or
constructs the whole `Prints`; `OneProof/RC/Wiring/KolyvaginBridge.lean:35,43`
adapts the rank-one case to the distinct pole input and its rank projection.
The latter lane is parked. Packed `Prints` and comment-only references do
not introduce additional Kolyvagin projections.
