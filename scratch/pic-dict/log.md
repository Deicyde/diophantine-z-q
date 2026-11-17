# pic-dict results log

Base e22df37cd (leaf-fold30). Rows: `T09Pic.PicZeroAbVar` (TailZ24:302), `T09Pic.PhiAmpleIsogeny` (TailZ24:366),
`T09Pic.WeilPairingMumford` (TailZ24:708); all three are fields of `HDec.HSyn.OpenAddedLeaves17` (TailZ34:111).

## 2026-11-16
- 02:59 started `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` (no prebuilt tree on this
  base anywhere on the host; output scratch/pic-dict/build.out).
- Findings (VERIFIED, read in source): `picardFunctor f` is `presheafToSheaf (fppfTopology.over S)` of
  `picardPresheaf f` (T ↦ Pic(X ×_S T), no quotient by Pic(T)); `toPicardFunctor` = `toSheafify`. Mathlib has
  `Presheaf.isLocallyInjective_toSheafify'` / `isLocallySurjective_toSheafify'` and
  `pointOfClosedPoint` (AlgClosed/Basic.lean). So L5 should be provable: every fppf covering sieve of Spec K̄
  contains the identity.
- The vendored library proves Kleiman 9.2.5 in general form (`Picard/Descent.lean`,
  `isIso_picardFunctorNormalized_ι_comp_toPicardFunctor`, under `IsIso pushforwardUnitMap` universally); not needed
  for L5.
- 04:00 build finished (62 min wall, exit 0).
- 04:45 scratch/pic-dict/Core.lean compiles (`lake env lean`, ~10 s after imports). VERIFIED, axioms
  [propext, Classical.choice, Quot.sound] for:
  - `PicDict.picPointsAlgClosed : T09Pic.PicPointsAlgClosed` (L5 is a theorem). Proof: every fppf covering sieve of a
    scheme contains every point with values in an algebraically closed field (induction on `Precoverage.Saturate`,
    Nullstellensatz `pointOfClosedPoint`), then Mathlib's `isLocallyInjective_toSheafify'` /
    `isLocallySurjective_toSheafify'`.
  - dictionary glue: `toPicardFunctor_picClass`, `picClass_mul`, `picClass_injective`, `picClass_gal`,
    `picClass_dual`, `picClass_phiL` (M_{λ_L x} = t_x^*L_K̄ ⊗ L_K̄⁻¹), `phiPt_translInv` (from the square),
    `exists_lift_pt`, `exists_pt_of_isClosed`, `surjective_of_forall_pt`.
  - `weilPairingMumford_of_printed` (9 Mumford-type leaves at A_K̄ + `WeilFormulaGalois` glue + field
    `PhiAmpleIsogeny`) : `T09Pic.WeilPairingMumford`.
  - `phiAmpleIsogeny_of_printed` (`MumfordKLFinite`, `MumfordPhiSurjective`, `AmpleBaseChangeAlgClosure`,
    `PicZeroPtsTranslInv` (composite), `FiniteOfFiniteKerPts` (glue)) : `T09Pic.PhiAmpleIsogeny`.
- 04:30-04:45 scratch/pic-dict/Transport.lean (VERIFIED, compiles, standard axioms): `pullbackObjUnitIso_comp`
  (pOUI compatible with pullbackComp, via the adjunction mate `conjugateEquiv_pullbackComp_inv`),
  pullbackComp coherence lemmas, `coherence_I`, `coherence_II`, `wf_transport` (Mumford's formula is carried by
  any `g` with `t' ≫ g = g ≫ t`, `g ≫ m = m ≫ g` to `g.appTop` of the formula), `wf_iso`, and
  `weilFormulaGaloisEx` (the Galois clause, transport along `1 × Spec σ`). Uses the vendored
  `pullbackObjUnitIso_conj_app_top` (FreeGeneratorPullback.lean).
- Merged into ZInQKernel/Contrib/OneProof/PicDictionary.lean; `lake build ZInQKernel.Contrib.OneProof.PicDictionary`
  succeeds. `#discharges` (scratch/pic-dict/discharges.txt):
  `DISCHARGES [OpenAddedLeaves17.weilPairingMumford] by PicDict.weilPairingMumford_of_printed` still assumes the
  9 Mumford-type leaves and `T09Pic.PhiAmpleIsogeny`; standard axioms.
- autofold dry-run (scratch/pic-dict/autofold.json, weilPairingMumford only, no --allow-rise):
  `strict count: 40/8 on 48 -> 48/8 on 56; strictest 39/9 -> 48/8`; with the three rows re-rated
  consequence GLUE/GLUE as lf31 does (temporary kinds.tsv edit, restored):
  `strict count: 37/11 on 48 -> 46/10 on 56; strictest 37/11 -> 46/10` (-1 strict, -1 strictest).
  The dry-run module compiles (`sixContactMin_of_open35`, standard axioms).
- ~05:00 `finiteOfFiniteKerPts` proved (scratch/pic-dict/Finite.lean; merged). `phiAmpleIsogeny_of_printed` now takes
  4 leaves (`MumfordKLFinite`, `MumfordPhiSurjective`, `AmpleBaseChangeAlgClosure`, composite `PicZeroPtsTranslInv`).
- ~05:10 `mumfordWeilDual_of_pairing : MumfordWeilPairing → MumfordWeilDual` proved by `Transport.wf_transport`
  along `f × 1` (scratch/pic-dict/Dual.lean; merged). `weilPairingMumford_of_printed` now takes 8 leaves +
  `PhiAmpleIsogeny`. VERIFIED: module builds; #discharges updated; dry-runs:
  weil only `40/8 on 48 -> 47/8 on 55; strictest 39/9 -> 47/8` (lf31 rating: `37/11 -> 45/10; 37/11 -> 45/10`);
  both rows `40/8 -> 47/9 on 56; strictest 39/9 -> 47/9` (lf31: `37/11 -> 46/10; 37/11 -> 46/10`).
  Both dry-run modules compile (sixContactMin_of_open35, standard axioms).
- ~05:15 `mumfordWeilCompat_of_pairing` proved (Transport.wf_transport₂, coherence_III; scratch/pic-dict/Compat.lean).
- ~05:25 AC restatement (scratch/pic-dict/AlgClosed.lean, merged): leaves for `k` algebraically closed and
  `X : AbVar k` with `X(k) = 𝟙_ ⟶ X.X`, `t_x = lift (𝟙, toUnit ≫ x) ≫ μ`, `n_X = 𝟙^n`, Mumford's `Pic⁰` =
  translation-invariant classes, Mumford's formula: `MumfordSquareAC`, `MumfordMulNPicZeroAC`,
  `MumfordPhiSurjectiveAC`, `MumfordWeilPairingAC`, `MumfordWeilNondegAC`, `MumfordWeilAltAC`, `MumfordKLFiniteAC`.
  Bridge to `A_K̄ := Over.pullback (Spec K̄ → Spec K)` of `A` proved: `tr_pts` (translations), `mul_AKbar`,
  `pts_mul`, `pts` bijective, `formula_bridge`; `*_of_ac` for each leaf. VERIFIED, standard axioms.
- Final: `weilPairingMumford_of_ac` (7 leaves + phiAmpleIsogeny), `phiAmpleIsogeny_of_ac` (4 leaves, one composite).
  #discharges: 11 lines discharge (both forms listed). Dry-runs (scratch/pic-dict/autofold.json):
  `40/8 on 48 -> 46/8 on 54; strictest 39/9 -> 46/8`; lf31 rating `37/11 -> 44/10; strictest 37/11 -> 44/10`.
  Both rows: `40/8 -> 46/9 on 55; 39/9 -> 46/9`; lf31 `37/11 -> 45/10; 37/11 -> 45/10`. Dry-run modules compile.
- ~05:40 scratch/pic-dict/TranslInv.lean (merged): `picZeroPtsTranslInv_of_leaves (hU : PushforwardUnitUniversal)
  (hGI : GeomIntegralProd) : PicZeroPtsTranslInv`. Proof: the vendored Kleiman 9.2.5 (`picardFunctorNormalizedIso`,
  hypothesis = hU) gives honest normalized classes on `A × T`; the renormalized `t_a^*c ⊗ c⁻¹` (`dT`) is natural in
  `T`; classifying it at `T = A ⊗ B` gives `Ψ : A ⊗ B → P`, trivial on both axes, landing in `B`, a homomorphism by
  `MulRigidity` (needs `A ⊗ B` geometrically integral = hGI), hence trivial; at `K̄`-points this is
  `t_x^*M_y = M_y`. VERIFIED, standard axioms.
- `phiAmpleIsogeny_of_leaves` (MumfordKLFiniteAC, MumfordPhiSurjectiveAC, AmpleBaseChangeAlgClosure,
  PushforwardUnitUniversal, GeomIntegralProd). Both-rows spec (scratch/pic-dict/autofold-both.json):
  this base `40/8 on 48 -> 48/8 on 56; strictest 39/9 -> 48/8` (no --allow-rise); lf31 rating
  `37/11 on 48 -> 47/9 on 56; strictest 37/11 -> 47/9` (-2 strict, -2 strictest). Dry-run module compiles.
  #discharges: 12 discharge lines (all forms).
- ~05:55 `ampleBaseChangeAlgClosure` proved (scratch/pic-dict/Ample.lean, merged): ampleness pulls back along an
  affine morphism (`isAmple_pullback`; vendored `Hom.comap_zeroLocus`, `coe_support_comap`, monoidal pullback).
- Final theorems: `weilPairingMumford_of_mumford` (MumfordSquareAC, MumfordMulNPicZeroAC, MumfordPhiSurjectiveAC,
  MumfordWeilPairingAC, MumfordWeilNondegAC, MumfordWeilAltAC; + field PhiAmpleIsogeny) and
  `phiAmpleIsogeny_of_mumford` (MumfordKLFiniteAC, MumfordPhiSurjectiveAC, PushforwardUnitUniversal,
  GeomIntegralProd). Dry-runs: weil only `40/8 -> 45/8 on 53; strictest 39/9 -> 45/8` (lf31 `37/11 -> 43/10`);
  both `40/8 -> 47/8 on 55; strictest 39/9 -> 47/8` (lf31 `37/11 -> 46/9; strictest 37/11 -> 46/9`). Both dry-run
  modules compile. #discharges: 14 discharge lines (all intermediate forms).
- Verbatim copies of the three rows (scratch/pic-dict/Verbatim.lean) compile and equal the originals by rfl (VERIFIED).
- ~06:05 `picZeroAbVar_of_leaves` (scratch/pic-dict/PicZero.lean, merged): `PicZeroAbVar` from `PicLocFinType`
  (Kleiman 9.4.8), `IdentityComponentLFT` (SGA 3 VI_A 2.4), `PicZeroSmooth` (pending reading), `PicZeroProper`
  (Kleiman 9.5.4). Glue proved: open subscheme on the identity component as a group object (`AVGlue.grpObjOfMono`,
  `liftV`), smooth ⇒ geometrically reduced (`isReduced_of_smooth_field`, via vendored
  `ZInQ.SmoothFibre.isReduced_of_smooth_of_field`), geometric integrality. VERIFIED, standard axioms.
  Spec scratch/pic-dict/autofold-all.json (three rows): this base `40/8 on 48 -> 49/9 on 58; strictest 39/9 -> 49/9`
  (needs --allow-rise); lf31 rating `37/11 -> 49/9; strictest 37/11 -> 49/9` (same as both-rows: the
  pending-reading leaf replaces the row). Dry-run module compiles. #discharges: 15 lines.
- ~06:20 `pushforwardUnitUniversal` proved (vendored `isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral`,
  Modules/StructureSheaf.lean) and `geomIntegralProd` proved (smooth ⇒ geometrically reduced, proved here; Mathlib's
  `GeometricallyIrreducible.comp`). Final theorems: `phiAmpleIsogeny_final (MumfordKLFiniteAC)
  (MumfordPhiSurjectiveAC)` and `weilPairingMumford_final` (7 Mumford leaves, no dependence on the field
  phiAmpleIsogeny). VERIFIED, module builds, standard axioms. #discharges: 17 lines (all forms).
  Dry-runs (this base / lf31 rating): weil only `40/8 -> 46/8 on 54; strictest 39/9 -> 46/8` /
  `37/11 -> 44/10; 37/11 -> 44/10`; both `40/8 -> 45/8 on 53; 39/9 -> 45/8` / `37/11 -> 44/9; 37/11 -> 44/9`;
  all three `40/8 -> 47/9 on 56; 39/9 -> 47/9` / `37/11 -> 47/9; 37/11 -> 47/9`. All three dry-run modules compile.
