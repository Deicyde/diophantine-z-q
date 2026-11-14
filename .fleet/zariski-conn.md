# zariski-conn (fleet summary)

**Main result.** frob-pieces' leaf candidate `FrobPiecesNeron.ProperSmoothGenConnected` (statement
verbatim) is reduced to ONE published leaf: Zariski's connectedness theorem,
`ZariskiConn.ZariskiConnectedness` (EGA III₁ 4.3.1 + 4.3.4, locators UNVERIFIED):
`∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), IsProper f → IsLocallyNoetherian Y →
 (∀ U : Y.Opens, Function.Bijective (f.app U)) → GeometricallyConnected f`
(i.e. proper, `f_*𝒪_X = 𝒪_Y` ⇒ non-empty geometrically connected fibres). Everything else is
proved: in particular `R → Γ(X, 𝒪_X)` bijective and `f_*𝒪_X = 𝒪_{Spec R}` for `X/𝓞_L[1/f]` smooth
proper with geometrically connected generic fibre, WITHOUT the finiteness of `f_*𝒪_X` (EGA III 3.2.1
not needed): integrality of global sections (Mathlib) + `Γ(X) ↪ Γ(X_L) = L` (flat base change of
scheme-theoretic dominance, Mathlib; Tau Ceti's `baseRingToGlobalSections_bijective_of_geometricallyIntegral`).

**Declarations proved** (all axioms `[propext, Classical.choice, Quot.sound]`):
- `ZInQKernel/Contrib/ZariskiConn/Basic.lean` (namespace `ZariskiConn`):
  `properSmoothGenConnected_of_zariskiConnectedness : ZariskiConnectedness.{0} → ProperSmoothGenConnected`
  (`ProperSmoothGenConnected` = verbatim copy of frob-pieces' def), `appTop_bijective_of_generic`,
  `app_bijective_of_appTop_bijective`, `dedekind_fractionRing_of_away`, helpers.
- `scratch/zariski-conn/ZariskiConnFull.lean` (namespace `ZariskiConnGlue`): `properSmoothGenConnected :
  ZariskiConnectedness.{0} → FrobPiecesNeron.ProperSmoothGenConnected`, `goodRedCofinite_of_neron_zariski`,
  `algFrobRed_of_neron_zariski_nmp`, `tateBridge35_of_neron_zariski_nmp`.

**What compiles.** `lake build ZInQKernel.Contrib.ZariskiConn.Basic`: success.
`scratch/zariski-conn/build.sh` → `ZariskiConnFull.lean` (cmp-identical copy of frob-pieces'
`FrobPiecesFull.lean` + Contrib import + `part_zc.lean`): `lake env lean` exit 0, 2 min 49 s,
122 `#print axioms` all standard, 0 sorryAx. `py/verbatim_check.py`: ALL VERBATIM.
11 Tau Ceti modules vendored unmodified (5a01f5fe, closure of `Geometrically.GlobalSections`);
NOTICE updated; diffcheck2 NOTE-ONLY 0, MOD-UNNOTED 0.

**What remains.** The leaf `ZariskiConnectedness` itself (needs the theorem on formal functions,
EGA III 4.1.5, and étale-local base change for 4.3.4; Mathlib v4.35 has no coherent cohomology or
formal schemes, Tau Ceti has no formal functions). Report: docs/research/zariski-conn.md; log:
scratch/zariski-conn/log.md.
