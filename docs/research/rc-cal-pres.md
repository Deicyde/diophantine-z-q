Scoped stop: the finite full/Kummer quotient presentations are constructed from the finite full cochain comparison and one check on the actual Kummer image. At a moving place the remaining comparison is to the two disks with differentials `χFr − 1` and `χFr − r`; at an active place it is to two disks with differential `2 · 1₂`. At precision zero every block presents the two zero modules. For positive precision this work does not discharge `presMov`, `presMov'` or `presAct` unconditionally. The unresolved assertions are about a specified comparison on full cochains, and about the projection of the Kummer **submodule** of full degree-one cohomology.

Manuscript error at tex 3471–3477: (4.4) states a short expression for the tame norm at a tame split prime without requiring `g² = 1`. The general norm is `1 + g + ⋯ + g^(q−1)`. For example, take `q = 5`, a rank-two rotation `g` with `g² = −1` over `ℤ/8`, and `Φ = 1`. The tame relation `g⁵ = g` holds. The norm is `1`, whereas the displayed expression is `3 + 2g` and its use gives `DC − CA = 4 · 1 ≠ 0`. Restricting (4.4) to involutive inertia corrects the displayed formula. For commuting tame actions with `g^q = g`, the same differential formula uses the full norm. Both central cases here have `g² = 1`; the Lean model already requires this. The counterexample concerns the unrestricted wording.

Put `V = A_i²` and let `F` be the first disk differential, `D` the second. Full cohomology of the split model is `H¹ = coker F × ker D`, `H² = coker D`. If projection to `coker F` restricts to an isomorphism on the Kummer submodule, the submodule is a graph. Subtracting that graph gives the quotient `ker D`, even if its singular coordinate is nonzero. All these are module equivalences over `A_i`.

At the moving places, the finite Tate coordinates give the actual arithmetic Frobenius `Φ = χFr`; both factors of the central module are unramified. The procyclic calculation applies to the **ordinary** disk: its degree zero is the invariants of `Φ` and its degree one the coinvariants. In the full tame model the **singular** differential is `Φ − r`, because Frobenius conjugates tame inertia by its `r`-th power. The ordinary and singular differentials are distinct.

At an active place, inertia acts by `−1` and the odd tame norm at that action is `1`. The actual action at precision one is trivial by rational two-torsion and the reduction of the quadratic sign. Thus the integral signed Frobenius satisfies `Φ − 1 = 2T` for an integral matrix `T`. The middle change of coordinates `(v,w) ↦ (−w, v + T w)` sends the differentials of (4.4) to `x ↦ (2x,0)` and `(y,z) ↦ 2z`. The remaining Kummer check here concerns the first coordinate `−w modulo 2`, i.e. inertia evaluation modulo two. It is not the unramified local condition.

## Statements and fields

The declarations below use the actual central character, local complex, and Kummer image from `GenuineLocalBlocks.lean`. The two moving places have separate Tate matrices. Supplying the corresponding comparison at each place gives the respective field for the canonical block in that basis; identifying any other block chosen by an assembly model with this one is separate.

| Declaration | Statement and field |
| --- | --- |
| `splitLocalModel` | The full three-term model has differentials `x ↦ (Fx,0)` and `(y,z) ↦ Dz`. Used by all three fields. |
| `splitLocalH1`, `splitLocalH2` | Linear equivalences from full model cohomology in degrees one and two to `coker F × ker D` and `coker D`, respectively. Used by all three fields. |
| `quotientOfFirstCoordinate` | For a submodule of `U × V` whose first projection is bijective, the quotient is linearly equivalent to `V`. Used for degree one in all three fields. |
| `activeMiddleCoordinates`, `activeMiddleCoordinates_d0`, `activeMiddleCoordinates_d1` | The map `(v,w) ↦ (−w,v+Tw)` is a linear equivalence, carries `(2Tx,−2x)` to `(2x,0)`, and twice its second component is `2v+2Tw`. Used by `presAct`. |
| `cx3Hom_isIso` (private) | A map of three-term models with identity end maps and a linear equivalence in the middle is a cochain isomorphism. Used in both normalizations. |
| `movingTameNormalization` | The augmented tame model at odd (q) is isomorphic as a cochain complex to the split model with `F = Φ − 1`, `D = Φ − q`. Used by `presMov` and `presMov'`. |
| `tameNorm_negId`, `activeTameNormalization` | For odd (q), `N_q(−1) = 1`; with `Φ − 1 = 2T` the sign-negative tame model is isomorphic as a cochain complex to the split model with `F = D = 2 · 1`. Used by `presAct`. |
| `kummerFirstCoordinate` | Compose inclusion of the genuine Kummer image, the map on full `H¹` of the comparison, and the first projection of `splitLocalH1`. Used by all fields. |
| `presentationOfSplit` | Given a full comparison inducing isomorphisms in degrees one and two and bijectivity of `kummerFirstCoordinate`, constructs both linear equivalences of `PresentsLocalQuotient` for the second disk. Used by all fields. |
| `movingPresentation`, `activePresentation` | Specialize that construction to the reductions of `movingOrdinary = χFr − 1` and `movingBlock = χFr − r·1₂`, or `activeBlock = 2·1₂` in both disks. Supply `presMov`/`presMov'` and `presAct`, respectively, once the finite inputs below are proved. |
| `presentationAtZero` | At `i = 0` the kernel, cokernel, genuine quotient of `H¹`, and genuine `H²` are zero modules. Supplies all three fields at zero precision. |
| `centralChar_coe`, `central_tmul_smul`, `central_smul_of_torsion_fixed` (private) | The central character is the reduced quadratic sign; the action on a pure tensor uses that sign and the actual torsion action; if torsion is fixed, only the sign acts. The proofs follow the private lemmas in the base lane. Used by all fields. |
| `centralSignedTateAction`, `signedReduced_subScalar`, `movingReduced_subScalar` | Finite Tate coordinates carry the actual local action to the reduction of the signed integral Tate matrix, including after subtracting any natural scalar. In the moving case the scalar is (1) or the actual residue norm (r). Used for both moving fields and the active evenness check. |
| `movingInertiaAction`, `activeInertiaAction` | The moving inertia action is the identity; the active action supplies an inertia element acting by minus one at every precision. Used at the respective places. |
| `activeSignedTate_subOne_even`, `activeReduced_apply` | Rational two-torsion and an active action force the signed integral Frobenius minus one to be twice an integral matrix; the reduction of `activeBlock` acts by two. Used by `presAct`. |

The cochain models are from tex 3470–3481. The active middle change, explicit subquotient algebra and the coefficient-level transport of the comparison are on-the-spot (provenance (c)). No new structure or Prop is used as a theorem input. The comparison hypotheses apply to the full complex before imposing any local condition. The Kummer hypothesis applies only to an ordinary-coordinate map in degree one; it says nothing about full `H²` or the singular disk. Neither assertion alone gives the presentation. The active Frobenius divisibility used in the abstract normalization is a statement about the coefficient action, independent of local cohomology.

## Remaining hypotheses and ownership

For each (i>0) and each of the two moving places or any active place, use the actual local complex `L = (centralLocalComplex W i v s hs hs0).toCC`. Choose (F,D) as in the opening paragraphs, reduced by `constRed i`. The candidate (c : L → (splitLocalModel F D).toCC) is the existing tame cochain map of (4.4), in the Tate coordinates, followed by the normalization above. The following are the exact positive-precision obligations at the implemented boundary:

| Remaining input | Exact assertion and scope | Owner and estimated size |
| --- | --- | --- |
| Actual tame comparison in degree one | `QuasiIsoAt c 1` (tex 3470–3481), with (g=1) at moving places and (g=-1) at active places. On cocycles the unnormalized map is `z ↦ (z(φ),z(σ))`. This is on **full** degree one. | Missing local theory. The existing `quasiIsoAt_tameCochainMap_one` is for field coefficients with (g=1) and specified generators. Extending it to `A_i` and handling (g=-1) are moderate proofs, roughly 150–350 lines after a compatible generator choice. |
| Actual tame comparison in degree two | `QuasiIsoAt c 2` (tex 3470–3481, 4066–4072, 4078–4079). For the existing `tameE` evaluation on 2-cocycles this means its image modulo `range d¹_model` is all of degree two of the model and its kernel modulo that range is precisely the continuous 2-coboundaries. No claim in higher degrees is needed. | Missing local theory. Existing cup and Euler characteristic work gives partial results, especially in residual unramified coefficients. A finite-ring proof for both actions is material, roughly 200–500 lines with the generator and comparison framework in place. |
| Choice for the two comparison proofs | At the odd completion choose `IsIwasawaTriple K v.1 φ σ P` as defined in `TamePlaceBridge.lean`: arithmetic Frobenius, tame inertia generator modulo a closed normal wild pro-(p) group, with the exact conjugation relation. Relate the generator actions to the moving/active actions; triviality of the finite 2-primary action on the wild group is required. For a moving presentation choose the Frobenius in its action record or compare lifts using trivial inertia. At an active place use good reduction for *all* untwisted inertia, and the ramified quadratic character for the tame generator. | Missing local theory (tex 3470–3477); separate substantial local ramification formalization (several hundred lines or more) if proving the existing `IwasawaGeneratorsAt` interface. The single witness in `ActiveLocalAction` is not a tame generating triple. The split good-prime arithmetic specialization remains an ELLIOT input from tex 2344–2347, 2720–2727 and 3500–3506. |
| Moving Kummer comparison | `Function.Bijective (kummerFirstCoordinate hFull c)` at each moving place (tex 3080–3085, 3413–3418, 3478–3481). A sufficient arithmetic statement is `im δ_i = im inflation(H¹(G_v/I_v,M_i))` inside genuine `H¹`, where `im δ_i` means the `A_i`-span of the actual Kummer image; inflation then reads as `coker(Φ−1)`. | Missing local theory. The tree proves the procyclic comparison (`urSelf_quasiIsoAt_one`) and, for point torsion, the good-reduction Kummer inclusion in unramified classes. The reverse inclusion and its coefficient/actual-map transport are a small-to-moderate bridge, roughly 100–250 lines with a local division or finite reduction proof. |
| Active Kummer comparison | `Function.Bijective (kummerFirstCoordinate hFull c)` at every active place (tex 3413–3418, 3442–3445, 4078–4079). Explicitly the (A_i)-linear map from the actual Kummer submodule given on a class by `[z] ↦ −z(σ) mod 2V` must be bijective. Coboundaries evaluate in (2V). | Missing local theory. Surjectivity can be checked using rational two-torsion and Kummer cocycles of their (2^i)-division points; injectivity additionally requires control of the size of the Kummer image, e.g. via local points away from two or the finite annihilator and perfect pairing. Roughly 150–350 lines on top of the relevant existing comparison and torsion transport. |

The two `QuasiIsoAt` and the Kummer projection assertions are the boundary actually consumed. In particular an all-degree quasi-isomorphism, a termwise contraction, an integral local model of the full complex, and a complete local duality theory are not additional hypotheses of these suppliers. The existing support-change and local duality print statements are not instantiated by these files. No print is added, including the existing broader tame comparison interfaces; an unread literature identification remains GLUE pending the lead's skeptic pass before any LEAF.

The inherited threshold `MilneLocalDualityOrder` is still used by the base **length** route (tex 3442–3445; print layer), and `FrobeniusTrace` is still used to identify the moving trace with the Euler coefficient (tex 3686–3691; global Frobenius owner). Neither is a new hypothesis of the conditional presentation. `hcentral` (tex 3483–3498, 4066–4080; local-to-global assembly owner), `KummerCoordinateBlockG.I` and `link` (tex 4007–4018, 4050–4064; ordinary Kummer calibration owner), `goodModel` (tex 4117–4127; companion component owner), and `PostLeaves.calibration` (cloud root) remain outside this task.

## Known issues

- The unrestricted tame norm in (4.4) needs the correction above. The statement of degree-two-only cohomology at tex 4078–4079 concerns the **integral** quotient. Its finite derived reduction can acquire degree-one cohomology. The finite model here retains that degree.
- `MilneLocalDualityOrder` gives lengths only. Equal finite orders by themselves do not identify the two (A_i)-modules.
- The manuscript's local free model (4.4) does not by itself identify which full (H^1) classes come from the genuine Kummer map at an active place. The first-coordinate criterion isolates that missing check.
- No external locator was taken from memory. The manuscript's citations and the statuses of existing in-tree interfaces are as recorded by their sources.

## Manuscript check

| Tex lines | Verdict and check |
| --- | --- |
| 2344–2347, 2720–2727 | OK — the odd split specialization and the coefficient ring and quadratic sign give the input used here. |
| 3080–3085 | unverified — equality of the moving Kummer image and the unramified image remains to be transported to these genuine finite coefficients. |
| 3413–3418, 3425–3432 | OK — the finite condition includes degree zero; `kummerImageH1` uses the actual map for the actual twist. |
| 3442–3445 | unverified — a finite duality/annihilator route could help prove the active Kummer projection is injective; it is not assumed here. |
| 3471–3477 | error — the displayed short norm needs involutive inertia; use the full tame norm in general. |
| 3470–3477 | gap filled — normalized the stated free-model differentials at inertia (+1) and (-1), including the active integral factor of two. |
| 3470–3477 | unverified — the candidate comparison with actual continuous cochains needs the generator choice and bijectivity in degrees one and two over every (A_i). |
| 3479–3481 | OK — ordinary `Φ−1` gives procyclic invariants and coinvariants, and the singular differential is `Φ−q`. The two disks are formally identified in the model. |
| 3483–3498 | OK — the moving specialization has trivial central inertia; the active computation does not use support removal. |
| 3686–3691 | OK — the reduction uses arithmetic Frobenius in the existing Tate basis; relating its trace to (a_r) is inherited. |
| 4032–4036, 4078–4080 | gap filled — the finite algebra of the active two disks is proved. The genuine Kummer identification remains as stated above. |
| 4066–4072 | gap filled — the reduced signed moving block, for either chosen split place, is the singular differential used by the conditional presentation. |
| 4073–4078 | unverified — determinant cancellation and the common limit are outside this task. |

## Verification

All three files compiled individually and serially with `lake env lean --threads=1` after resource checks. The 29 recorded `#print axioms` outputs (including the private proof helpers) report only `propext`, `Classical.choice` and `Quot.sound`, or a subset. See the [results log](../../scratch/rc-cal-pres/log.md) for the individual compile outcomes.
