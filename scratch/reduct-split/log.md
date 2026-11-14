# reduct-split results log

Setup: compile checks with `scratch/reduct-split/chk.sh FILE` = `lean` with LEAN_PATH on a symlink tree
`~/rs-lib` of ~/dzq-check2's build (same commit 5da857b0, `git diff 5da857b0 HEAD -- ZInQKernel` empty) plus
`ZInQKernel/OneProof/H/TailY.olean` compiled out of tree (17 s, unchanged source). One Lean process at a time.

## Compile outcomes
- 11:25 Reduction.lean §1 (divisibility: `exists_pow_eq`, `exists_tate_lift` from `PkgI2.TorsionStructure.{0}`): OK, 4 s. VERIFIED.
- 11:30 Reduction.lean §2-§6: definitions `GroupModelO`, `IsNeronModel`, `geomSpecialFibre`, `IsSemistable`,
  `SemistableNeronModels`, `HasSemistableReduction`, `TΩ`, `galTΩ`; leaves `NeronSchemeModelExistsDVR` (BLR 1.4/3),
  `SemistableUnipotent` (SGA 7 IX 3.5 ⇒), `RaynaudSemistable` (SGA 7 IX 4.7), `SemistableReductionDVR` (SGA 7 IX 3.6);
  glue `DVRFiniteExtension`, `FixedTorsionRational`; theorems `raynaudCriterion_of_leaves : ... → PkgI2.RaynaudCriterion.{0}`,
  `grothendieckMonodromy_of_leaves : ... → PkgI2.GrothendieckMonodromy.{0}`: OK, 8 s. VERIFIED (axioms not yet printed).
- 11:33 Reduction.lean §7: leaf `SerreTateThm2` (Serre–Tate 1968 Thm 2, finite image of inertia on T_ℓ), glue
  `TorsionFieldOfDefinition`; proved `finite_image_of_open` (⇐ direction of the finite-image/open-subgroup equivalence,
  no glue) and `open_of_finite_image` (⇒, from the glue + divisibility); `serreTatePotentialGood_of_leaves : SerreTateThm2 →
  TorsionStructure → TorsionFieldOfDefinition → PkgI2.SerreTatePotentialGood.{0}`. OK 10 s. Axioms of the three row
  theorems: [propext, Classical.choice, Quot.sound]. VERIFIED.
- 11:38 §8: `GroupModelO.transport`, `semistableNeronModels_transport`, `bcbcIso` (`(A_{K'})_L ≅ A_L` via Mathlib's
  `mapGrpCompIso`, `mapGrpNatIso (Over.pullbackComp ..)`), `bcbcIso_isMonHom`: OK. VERIFIED.
- 11:40 `SemistableReductionDVR` restated at every place of `K'` over `O` (the printed scope; r8 uses the place `w ∩ K'`).
  §9: leaf `SemistablePersistsDVR` (SGA 7 IX 3.3, finite extensions), glue `DVRComapFinite`, `SemistableLocalGlobal`,
  `SemistableAlmostAll`; `semistablePersists_of_leaves : ... → ZInQ.HeightSplit.SemistablePersists`,
  `semistableReductionThm_of_leaves : ... → ZInQ.HeightSplit.SemistableReductionThm`: OK 11.5 s; all five row theorems
  depend on [propext, Classical.choice, Quot.sound]. VERIFIED.
- 11:44 §10: `exists_fixing_field` (every K̄-point of a K-scheme locally of finite type is fixed by Aut(K̄/K'') for a
  finite K'' ⊆ K̄: affine open, Spec.preimage, finite type generators, IntermediateField.adjoin), hence
  `torsionFieldOfDefinition_of : TorsionStructure → TorsionFieldOfDefinition` (glue PROVED) and
  `serreTatePotentialGood_of_printed : SerreTateThm2 → TorsionStructure → PkgI2.SerreTatePotentialGood.{0}`. OK. VERIFIED.
- 11:45 §11: `raynaudCriterion_final`, `grothendieckMonodromy_final`, `serreTatePotentialGood_final` over the bundle leaf
  `AvSplit.MumfordTorsionAlgClosed` (via kernel `AvSplit.torsionStructure_of_mumford`). All axioms standard. VERIFIED.
  => r7b DONE (published-form leaves only: Serre–Tate Thm 2 + Mumford §4). r6: one glue (FixedTorsionRational). r8: one
  glue (DVRFiniteExtension).
- 11:46 §12 SS2: leaf `IdentityComponentBaseChangeDVR` (SGA 7 IX 3.3 second assertion, weakened to "open immersion into
  𝒩'"), glue `SemistableNeronBaseChangeLocalGlobal` (carries the global content: identity component over 𝓞_L, gluing),
  `semistableNeronBaseChange_of_leaves`: OK.
- 11:52 §13 faltingsLemma5BC: `gmTransport` (group model transport along a group iso of generic fibres; generic in the iso —
  a concrete `bcbcIso` inside the structure gave a kernel deterministic timeout, see memory note on iso chains),
  `gmTransport_isNeronModel`, `_isSemistable` (rfl), `_height` (MetrizedModel data depend only on `model.G`), glue
  `IsogenyBaseChangeDeg`; `faltingsLemma5BC_of_base : HeightSplit.FaltingsLemma5 → IsogenyBaseChangeDeg →
  HeightSplit.FaltingsLemma5BC`: OK 11.8 s; all axioms standard. VERIFIED.
- 11:54 §14: `exists_rational_of_fixed` (perfect K: an Aut(K̄/K)-fixed K̄-point of a K-scheme loc. of finite type is
  K-rational; affine open + `InfiniteGalois.mem_range_algebraMap_iff_fixed`), so `FixedTorsionRational` holds for
  perfect K; glue narrowed to `FixedTorsionRationalImperfect`; `raynaudCriterion_final'`. OK. VERIFIED.
- 11:59 §15: `dvrComapFinite : DVRComapFinite` PROVED (restriction of the ℤᵐ⁰-valuation of O'; value group a subgroup
  of ℤᵐ⁰ˣ, cyclic; nontrivial because the constant term of minpoly(ϖ') dominates; Mathlib
  `Valuation.valuationSubring_isDiscreteValuationRing`). `semistablePersists_final`, `semistableReductionThm_final`
  without that glue. All axioms standard. VERIFIED.
- 12:05 §16: `linearIndependent_of_distinct_cosets`, `dvr_of_finiteExt` (valuation ring of a finite extension over a DVR
  is a DVR: value group G of O' contains H = ⟨v'(ϖ)⟩ with [G:H] ≤ [K':K] by linear independence; g ↦ g^[G:H] embeds G
  into the cyclic H; Mathlib `valuationSubring_isDiscreteValuationRing`), `dvrFiniteExtension : DVRFiniteExtension`
  PROVED; `grothendieckMonodromy_final'` without glue. All axioms standard. VERIFIED.
  => r8 DONE (published-form leaves only: SGA 7 IX 3.6, 3.5, BLR 1.4/3, Mumford §4).
- 12:09 §17: `bcPt_comp` (bcPt natural in φ), `one_left`, `exists_ker_lift` (ker φ points descend from Ω₂ to K̄: the
  pullback of φ along the unit section is finite over K, kernel `exists_lift_of_isFinite`), `isogenyBaseChangeDeg :
  IsogenyBaseChangeDeg` PROVED (φ_L finite/surjective via CloudW01's `overPullback_isPullback`; Nat.card equality via
  bcPt and extPt). `faltingsLemma5BC_final : HeightSplit.FaltingsLemma5 → HeightSplit.FaltingsLemma5BC`. Axioms standard.
  VERIFIED.
- 12:11 §18: bundles `ReductLeaves` (8 published-form leaves), `ReductGlue` (4 glue), `rows_of_leaves` giving all seven split rows (+ HeightSplit.FaltingsLemma5 for faltingsLemma5BC). Axioms standard. VERIFIED.
