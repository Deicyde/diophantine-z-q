# Appendix E (K1)/(E.1): results log

Sizing (before any Lean build):

- VERIFIED: `KatoXi 2 Sig` forbids every odd divisor in `Sig`. Both source and target are required by `es_euler`. For this family, the exact range for the full level on the cofinal tail is `Disjoint fam.support Sig`; it also implies the primitive indices are in range. If an odd prime of `N₀ ℓ` appears in the family, it is in every allowed `Sig` and prevents this use even when it divides every `h x`. Indeed `BinaryFamily.single` at any signed odd squarefree parameter satisfies the local condition. Extra odd primes of the witness `Sig` also exclude families. Enlarging `Sbad` to contain the conductor support cannot help, since `Sbad ⊆ Sig`.
- VERIFIED: the manuscript's Σ at tex 6993 indexes the **twisted** system in `m`, not the untwisted argument `D*m`. Its smoothing exclusions depend on `F`; `c,d_s` avoid `F` by (K5), but an odd common prime of `N` need not. Tex 7089 uses the separate range of Proposition 8.12 for the untwisted classes. The existing (13.1.1) interface has no field for that wider range. The full print's hypotheses have not been reread.
- VERIFIED: `KatoZetaInterface.s` is a single nonzero complex scalar with no fields for `c,d_s`, no relation to `s_F` and no family-dependent choice. Equal valuations of the manuscript's scalars would not imply equality. The lattice scaling in tex 6920–6922 is also absent.
- VERIFIED: (E.1) at a finite level reduces to the equality of added prime supports, transitivity of the unnormalized transfer and semilinearity for the character-weighted group-ring map. The `EulerSystemData` corestrictions are additive maps without transitivity or deck equivariance fields. `KatoZetaInterface.recip` proves more than nonvanishing of the input class when the same quadratic weights are used: the abstract weighted deck sum has a nonzero period. Passing this to specialization requires a comparison, and rational nonvanishing must survive inverting two.
- VERIFIED: the tree has continuous cohomology, inverse Shapiro, its norm identity, and Mackey vanishing for a genuine open subgroup and discrete coefficients. It lacks a map from the abstract slots to these groups (including maps at every precision). Character factorization through the correct finite cyclotomic groups and the real-quotient identification must be supplied. Existing `cycS` takes roots of unity in `KS` as input and is a monoid hom, not by itself the packaged finite tower.
- VERIFIED: `TateS` is the actual inverse limit of torsion; `Lev` and its projections exist. `TLam` and `lamToAcoef` cover a scalar power-series action with finite truncations. They do not identify the actual cyclotomic group-ring tower with those truncations. `FreeModels` proves inverse-limit algebra for degreewise surjective complexes, not the completed Kato comparison.
- SPECULATIVE size: finite group-ring algebra small; open subgroup cochain constructions reusable; arithmetic comparison substantial (hundreds of lines just for explicitly compatible maps once the localization and cyclotomic identifications exist; potentially several thousand for the integral inertia groups and lattice realization). No need to construct Kato's regulator in this lane if the input interface is first given an actual realization. No downstream Appendix E steps planned.

Coefficient stage:

- VERIFIED (Lean): `weightedMap_single`, `weightedMap_invDeck`, `weightedMap_comp`, `specialize_familyMap`, `weightedMap_quotient` and `weightedMap_fullWeight_single` compile; see the corresponding compile and axiom outputs. The weighted map acts on group rings over both the integral and finite coefficient rings.
- VERIFIED (build audit): Lake bypassed the serialization shim in the initial dependency build by selecting its colocated Lean binary; that build was interrupted. The one-process limit was not enforced on that attempt. Later builds explicitly select the serialized Lean entry point, with a host load and available memory check before each compiler invocation. The initial failed draft check is not an axiom result.

Finite identity stage:

- VERIFIED (Lake): the Kato and family imports built with the serial compiler wrapper. Compatible compiled artifacts were reused only when the source closures agreed byte for byte.
- VERIFIED (Lean): the full-index range is exactly disjointness from `Sig`; the primitive divisor introduces exactly `unusedPrimes`; repeated two introduces no factor on the covered range. `finite_e1` gives the product formula from that norm and the two transfer laws, with `constituentWeight` retaining both conductor parts. The signed deck sum detected by the abstract reciprocity field is not killed by any nonzero natural number. All twelve finite-identity axiom checks pass.

Shapiro stage:

- VERIFIED (Lean and Lake): the Shapiro imports built; `ShapiroTransfer.lean` proves naturality of inverse Shapiro for the upper coefficient map, then equality with unnormalized corestriction on continuous cochains and on `H¹`. All four axiom checks pass. This proves the map-level bridge independently of the arithmetic identification of the retained input and the finite cyclotomic tensor representation.

Tensor coefficient stage:

- VERIFIED (Lean and Lake): `CoefModule`, `Cyclotomic` and `Tate` built. `CoefficientCohomology.lean` puts the integral scalar map on the coefficient tensor with the transported action, induces the continuous `H¹` map, and proves the inverse-deck formula for that action. All three axiom checks pass.

Comparison stage:

- VERIFIED (Lean): `Comparison.lean` states `KatoFiniteComparison` and `FixedKatoFiniteComparison` over the actual open cyclotomic kernels in `G_{ℚ,S}` and the actual torsion coefficients, with the concrete reduction, norm and deck maps. Given the comparison, `exists_nonzero_image_of_anchored_weightedSum` detects the anchor at a finite precision. Its axiom check passes. This proof does not assert the comparison or identify the detected class with a specialization of a completed family class.
- VERIFIED (verification): all five source checks and all 26 `#print axioms` checks passed. The initial build control incident is recorded above; the successful targeted dependency builds and individual checks were serial. No new print was added. The completed class, arithmetic comparison and uniform lattice bound remain open.
