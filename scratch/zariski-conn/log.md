# zariski-conn results log

Target: `FrobPiecesNeron.ProperSmoothGenConnected` (scratch/frob-pieces/part_neron.lean), statement verbatim.

## Survey: Mathlib v4.35 (pinned 56a00585) and Tau Ceti (VERIFIED by grep/read, 2026-11-13 11:45-12:00)
- Proper morphisms: `IsProper`, `UniversallyClosed`, valuative criteria (Morphisms/Proper.lean,
  ValuativeCriterion.lean). VERIFIED.
- Global sections of proper/universally closed: `isIntegral_appTop_of_universallyClosed`
  (Morphisms/Proper.lean:137: `f.appTop.hom.IsIntegral` for `[UniversallyClosed f] [IsAffine Y]`),
  `isField_of_universallyClosed`, `finite_appTop_of_universallyClosed` (over a field, finite type,
  integral X). VERIFIED.
- Direct images / coherence: NO coherent sheaves, no higher direct images, no finiteness of `f_*𝒪_X`
  for proper `f` over a noetherian base in Mathlib v4.35. `Modules/` has only Presheaf, Sheaf, Tilde.
  VERIFIED (ls/grep).
- Theorem on formal functions, Stein factorization, Zariski connectedness: NOT in Mathlib v4.35
  (grep "Stein", "formal functions", "connectedness": no hits). VERIFIED.
- Relative normalization `Scheme.Hom.normalization` (Normalization.lean; integral closure of 𝒪_Y in
  f_*𝒪_X, `IsIntegralHom f.fromNormalization`, commutes with smooth base change, stacks 03GV) and
  Grothendieck's Zariski Main Theorem (ZariskisMainTheorem.lean: quasi-finite locus open,
  `IsFinite.of_isProper_of_locallyQuasiFinite`). VERIFIED. (Not used: positive-dimensional fibres.)
- Finite morphisms: `IsFinite`, `IsIntegralHom` (Morphisms/Finite.lean, Integral.lean). VERIFIED.
- Geometric connectedness: `GeometricallyConnected` (Geometrically/Connected.lean): ConnectedSpace
  (hence nonempty) of every fibre over a field point. No "fibres of proper f with f_*𝒪=𝒪 connected".
  VERIFIED.
- Flat base change of sections: `isIso_pushoutSection_of_isQuasiSeparated_of_flat_right`
  (Morphisms/Flat.lean:452); schematic dominance stable under flat base change
  `IsSchemeTheoreticallyDominant.pullbackFst` and `Scheme.Hom.app_injective`
  (SchemeTheoreticallyDominant.lean). VERIFIED.
- Sheaf iso on a basis: `TopCat.Sheaf.isIso_iff_isIso_basis` (Topology/Sheaves/SheafCondition/Sites.lean:257);
  qcqs localization `isLocalization_basicOpen_of_qcqs`. VERIFIED.
- Tau Ceti oct16 (5a01f5fe): `Geometrically/GlobalSections.lean`:
  `Scheme.baseRingToGlobalSections_bijective_of_geometricallyIntegral` (universally closed,
  geometrically integral over a field k ⇒ k → Γ(X,𝒪) bijective). Vendored here (11 new modules,
  scratch/zariski-conn/vendor-new.txt, tcport.py, unmodified). Tau Ceti main (reference only) has
  sheaf cohomology, higher direct images, cohomology and base change, semicontinuity, but no theorem
  on formal functions / Zariski connectedness / Stein factorization (grep). VERIFIED.
- `lake build ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Geometrically.GlobalSections`: success,
  26 s (VERIFIED).

## Plan (special case over 𝓞_L[1/f])
- R ≅ 𝓞_L[1/f] is a Dedekind domain with fraction field L. For X/R smooth proper with geometrically
  connected generic fibre: R → Γ(X,𝒪_X) is bijective, WITHOUT finiteness of f_*𝒪_X:
  Γ(X) integral over R (Mathlib), Γ(X) ↪ Γ(X_L) (flat base change of the schematically dominant
  Spec L → Spec R), Γ(X_L) = L (Tau Ceti; X_L geometrically integral by smooth + geom. connected),
  R integrally closed in L. So EGA III 3.2.1 is NOT needed.
- Remaining input: Zariski's connectedness theorem (EGA III₁ 4.3.1 + 4.3.4) as the only leaf.

## Reduction proved (VERIFIED, compiled 12:25)
- ZInQKernel/Contrib/ZariskiConn/Basic.lean (`lake build ZInQKernel.Contrib.ZariskiConn.Basic`: success):
  - `ZariskiConn.ZariskiConnectedness` (LEAF, EGA III₁ 4.3.1 + 4.3.4, UNVERIFIED locators):
    `∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), IsProper f → IsLocallyNoetherian Y →
     (∀ U : Y.Opens, Function.Bijective (f.app U)) → GeometricallyConnected f`.
  - `ZariskiConn.ProperSmoothGenConnected`: verbatim copy of frob-pieces' def.
  - `appTop_bijective_of_generic` (R integrally closed domain, K = Frac R, p flat universally closed,
    generic fibre geometrically integral ⇒ R → Γ(X) bijective);
    `app_bijective_of_appTop_bijective` (Y affine, f qcqs, bijective on Γ ⇒ bijective on all opens;
    via `bijective_of_isLocalization_away`, `isLocalization_of_eq_basicOpen`,
    `TopCat.Sheaf.isIso_iff_isIso_basis` with the basic-open basis);
    `dedekind_fractionRing_of_away`;
    `properSmoothGenConnected_of_zariskiConnectedness : ZariskiConnectedness.{0} → ProperSmoothGenConnected`.
  - #print axioms (scratch/zariski-conn/axioms.lean): all four [propext, Classical.choice, Quot.sound].
- Pitfalls: `IsIso φ` for a `TopCat.Sheaf` morphism is not seen through `sheafToPresheaf`; use
  `TopCat.Sheaf.forget`. `Sheaf` morphism from `f.c`: `⟨f.c⟩`.

## Single-file check (VERIFIED, 12:45)
- build.sh → ZariskiConnFull.lean = src_FrobPiecesFull.lean (cmp-identical to
  scratch/frob-pieces/FrobPiecesFull.lean; that file is up to date with frob-pieces' build_full.sh
  inputs, cmp) + `import ZInQKernel.Contrib.ZariskiConn.Basic` after its 21 import lines + part_zc.lean.
- part_zc: `ZariskiConnGlue.properSmoothGenConnected : ZariskiConnectedness.{0} →
  FrobPiecesNeron.ProperSmoothGenConnected` (the Contrib copy is definitionally the same def),
  `goodRedCofinite_of_neron_zariski`, `algFrobRed_of_neron_zariski_nmp`,
  `tateBridge35_of_neron_zariski_nmp`.
- Prerequisite: `lake build` of the 21 imported ZInQKernel modules (builds lean/ ZInQ helpers;
  otherwise "unknown module prefix 'ZInQ'").
- Run 1: `lake env lean scratch/zariski-conn/ZariskiConnFull.lean` exit 0, 2 min 49 s, 122 axiom
  prints all [propext, Classical.choice, Quot.sound], 0 sorryAx (run1.txt).
- py/verbatim_check.py: ALL VERBATIM (Contrib copy and assembled file).
- NOTICE entry for the 11 vendored modules; diffcheck2: NOTE-ONLY 0, MOD-UNNOTED 0.

## Further split of the leaf: not done (assessment)
- 4.3.4 from 4.3.1 needs étale neighbourhoods with prescribed residue field + flat base change of
  f_*𝒪 (Mathlib has the latter) and "connected over k_sep ⇒ geometrically connected" (EGA IV₂ 4.5,
  missing in Mathlib). 4.3.1 from 4.1.5 needs formal completions and lim H⁰(X_n): missing.
