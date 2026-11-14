# reduct-glue results log

Setup: `Base.lean` = verbatim copy of `scratch/reduct-split/Reduction.lean` (namespace `ReductSplit`); new work in
`Body.lean` (namespace `ReductGlue`, during development imports `ReductSplitBase` = Base compiled to /tmp/rglib with
`lake env lean -o`); `mk.sh` concatenates both into the deliverable `ReductGlue.lean` (imports kernel modules only).
Kernel deps built in the worktree with `lake build` (all up to date). One Lean process at a time.

## Compile outcomes
- 12:29 Base.lean (copy) compiles, 15 s, all reduct-split `#print axioms` standard. VERIFIED.
- 12:55 Body §1: `mem_range_of_isSeparable_of_fixed` (separable + Aut(K̄/K)-fixed ⇒ in K: separable closure is Galois,
  `AlgEquiv.liftNormal`, `InfiniteGalois.mem_range_algebraMap_iff_fixed`); `isSeparable_of_etale` (image of an étale
  K-algebra in K̄ is separable: image is an intermediate field, `FormallyUnramified.of_surjective`,
  `FormallyUnramified.isSeparable`); `exists_rational_of_fixed_etale` (fixed K̄-point of an étale K-scheme is rational);
  `fixedTorsionRational_of_mulEtale : AvSplit.T4.MulEtaleAbelianScheme → FixedTorsionRational` (A[m] := pullback of
  [m] along the unit section, étale by base change); hence glue **`FixedTorsionRationalImperfect` PROVED** from the
  bundle leaf `MulEtaleAbelianScheme` (BLR 7.3/2), and `raynaudCriterion_leaves` (r6 from leaves only). OK. VERIFIED.
- 13:40 Body §2 (DVRs of a number field): `int_mem` (𝓞_L ⊆ O), `toOL`, `center O = 𝓞_L ∩ 𝔪_O`, `center_isMaximal`,
  `mem_iff_exists` (**O = (𝓞_L)_{𝔭_O}**: x ∈ O ↔ x·s = a with s ∉ 𝔭_O; via `ValuationRing.cond` in the DVR
  `Localization.AtPrime 𝔭`), `eq_of_center_eq`, `locToO`, `resIso : κ(𝔭_O) ≃+* κ(O)`, `barIso : κ̄(𝔭_O) ≃+* κ̄(O)`
  with `barIso_comp` (compatible with 𝓞_L), `dvrAt 𝔭` (𝔭-adic valuation ring, DVR) with `center_dvrAt`. OK. VERIFIED.
- 13:20 Body §3 (`SemistableAlmostAll`): `abelianScheme_neron` (abelian scheme over a DVR has the full Néron mapping
  property, bridged from the vendored FLT theorem in `Contrib/CloudW03NeronSurj`), `hasSemiAbelian_of_iso`,
  `hasSemiAbelian_of_abVar` (U = G, π = 𝟙, torus rank 0), `groupModelOfAbScheme`,
  `hasSemistableReduction_of_goodReduction`, `finite_dvr_mem_center` (`Ideal.finite_factors` + `eq_of_center_eq`),
  **`semistableAlmostAll_of : FrobPiecesNeron.AbVarSpreadsOut → FrobPiecesNeron.ProperSmoothGenConnected →
  SemistableAlmostAll`** (glue PROVED from kernel leaf/glue already in the build). OK. VERIFIED.
- 13:20 Base.lean with the extra imports CloudW03NeronSurj.Main (imports Mathlib) and FrobChain.Pieces: compiles
  unchanged (83 s). VERIFIED.
- 13:35 Body §4 (`SemistableLocalGlobal`): `isoX`, `neronO_unique` (Néron models over a valuation ring are unique as
  group schemes; postcomposition is a homomorphism on T-points for smooth T = 𝟙_, 𝒩⊗𝒩), `isSemistable_of_iso`,
  `semistableNeronModels_of_has`; `pbCompIso`, `toO 𝒩 O` (base change 𝒩 ×_{𝓞_L} O as a `GroupModelO`), `fibreIso`
  (geometric special fibre of 𝒩_O ≅ σ^*(geomFibre 𝒩 𝔭_O), σ = barIso), new LEAF `NeronLocalizesDVR` (BLR §1.2
  Prop. 4, UNVERIFIED number), new GLUE `SemiAbelianFieldIsoInvariant` (transport along a field isomorphism);
  **`semistableLocalGlobal_of : NeronLocalizesDVR → SemiAbelianFieldIsoInvariant → SemistableLocalGlobal`**. OK.
  VERIFIED.
- 13:40 Assembled `ReductGlue.lean` (mk.sh): compiles, 31 s. VERIFIED.
- 14:15 Body §5: `sσ`, `homEquiv_mul'`, `algK`, `ιR`, `Φ` (`(Spec R/k' ⟶ U_{k'}) ≃* (Spec R/k ⟶ U)` via
  `Over.mapPullbackAdj`), `Φ_comp`, `Φ_natural`, `hasSemiAbelian_pullback` (base change along a field iso preserves
  semi-abelian identity components: open immersion/flat/surjective by conjugating with the iso `pullback.fst`,
  connectedness by `Scheme.homeoOfIso`, `B_{k'}` built from base-change instances, torus via `Φ`);
  **`semiAbelianFieldIsoInvariant : SemiAbelianFieldIsoInvariant` PROVED**; hence
  **`semistableLocalGlobal_leaf : NeronLocalizesDVR → SemistableLocalGlobal`**. OK. VERIFIED.
- 14:50 Body §6 (printed bases): defs `IsStrictlyHenselianDVR` (DVR, `HenselianLocalRing`, residue field
  `IsSepClosed`), `IsCompleteDVR` (`IsAdicComplete 𝔪`); printed-base leaves `SemistableUnipotentSH`,
  `RaynaudSemistableSH`, `SemistableReductionSH`, `SemistablePersistsSH`, `IdentityComponentBaseChangeSH`,
  `SerreTateThm2Complete`; `printed_of_general` (each is a specialization of reduct-split's leaf). §7 machinery:
  `comapHom_isLocalHom`, `resMap`, `barIsoDVR` (κ̄(O) ≅ κ̄(O') for algebraic residue extension), `bcDVR` (base change
  of a `GroupModelO` along O ⊆ O'), **`isSemistable_bcDVR_iff`** (semistability invariant under such base change).
  OK. VERIFIED.
