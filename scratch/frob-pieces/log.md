# frob-pieces results log

## Setup (2026-11-13 09:28)
- Merged origin/wip/alg-frob-red (94799bde, "fleet summary (final)"). Open inputs of
  `AlgFrobRedRed.algFrobRed_of_gen`: GoodRedCofinite, SmoothGeomConnIntegral, FExtendGen, AbsFrob
  (plus kernel leaf I2-Red).
- AbsFrob: already proved by task afr-absfrob (origin/wip/afr-absfrob 1c158440,
  scratch/afr-absfrob/AbsFrobDef.lean, "AbsFrob proved from Mathlib"). Not redone here.

## SmoothGeomConnIntegral: PROVED (VERIFIED, compiled)
- Tau Ceti commit 5a01f5fe (tc-oct16) has `TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`
  (instance, {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [GeometricallyConnected f] :
  GeometricallyIntegral f), module AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral;
  import closure 11 modules, 1 already vendored (RingTheory.Kaehler.FormallyEtale).
- Vendored the other 10 with tcport.py (unmodified; list scratch/frob-pieces/vendor-new.txt;
  NOTICE entry added). `lake build ...Smooth.GeometricallyIntegral`: success, 17 s.
- diffcheck2: NOTE-ONLY 0, MOD-UNNOTED 0 (VERIFIED).
- ZInQKernel/Contrib/FrobPieces/SmoothGeomConnIntegral.lean: verbatim copy of the def
  (py/verbatim_check.py: True) and `FrobPieces.smoothGeomConnIntegral : SmoothGeomConnIntegral`.
  lake build: success (29 s). #print axioms: [propext, Classical.choice, Quot.sound] (VERIFIED).

## GoodRedCofinite: reduced to AbSchemeSpreadsOut (VERIFIED, compiled)
- New Prop `FrobPiecesGood.AbSchemeSpreadsOut` (leaf candidate, published; spreading out, EGA IV₃
  8.8.2, 8.10.5, IV₄ 17.7.8, IV₃ 9.7.7, UNVERIFIED locators): A/L extends to an abelian scheme
  (PkgI2.IsAbelianScheme) over a finitely generated subring ℤ[s] ⊆ L (s : Finset L), generic fibre
  ≅ toGrp A as group objects.
- Proved: `isUnit_intCast_of_coprime` (y prime to p is a unit of O_w, w ∣ p),
  `pullbackGrp_congr`, `goodRedCofinite_of : AbSchemeSpreadsOut → GoodRedCofinite`
  (S = prime factors of y, y from Mathlib's `exists_integral_multiples ℤ ℚ s`; ℤ[s] ⊆ O_w;
  base change of 𝒜 along Spec O_w → Spec ℤ[s]; generic-fibre iso from `Functor.mapGrpCompIso`,
  `Functor.mapGrpNatIso (Over.pullbackComp _ _).symm` (monoidality automatic,
  `NatTrans.IsMonoidal.of_cartesianMonoidalCategory`)).
- part_final: `smoothGeomConnIntegral : AlgFrobRedRed.SmoothGeomConnIntegral` (= the Contrib proof,
  definitional), `algFrobRed_of_spread : AbSchemeSpreadsOut → I2-Red → FExtendGen → AbsFrob →
  AlgFrobRed`, `algFrobRed_of_four` (GoodRedCofinite in place of AbSchemeSpreadsOut),
  `tateBridge35_of_spread`.
- Assembly: scratch/frob-pieces/build.sh → FrobPieces.lean (src_AlgFrobRed.lean cmp-identical to
  scratch/alg-frob-red/AlgFrobRed.lean, + Contrib import, + part_good, part_final).
- Run 2: `lake env lean scratch/frob-pieces/FrobPieces.lean`: exit 0, ~2 min 20 s, 94 axiom prints,
  all [propext, Classical.choice, Quot.sound], 0 sorryAx (VERIFIED; scratch/frob-pieces/run2.txt).
- Pitfall: in the assembled file `open MonObj` (from frob-trace's part) makes `mul_assoc`,
  `one_mul` resolve to MonObj lemmas; write `_root_.mul_assoc`.
- Dev loop: compiled AlgFrobRed.lean once to /tmp olean (`lake env lean -o`), then
  `LEAN_PATH=$(lake env printenv LEAN_PATH):/tmp/... lean dev.lean` with `import AlgFrobRed`
  (~20 s per iteration instead of ~2 min).
- Note: task afr-absfrob (origin/wip/afr-absfrob) is drafting FExtendGen from I2-NMP
  (part_fext.lean, 09:27); not duplicated here.

## GoodRedCofinite: second reduction, to neron-lg's N1-g1 + ProperSmoothGenConnected (VERIFIED)
- part_neron.lean: verbatim copies of neron-lg's `HasAbelianSchemeAway`, `AbVarSpreadsOut`
  (scratch/neron-lg/NeronLG.lean L449-469, same opens; py/verbatim_check.py: True).
- New Prop `FrobPiecesNeron.ProperSmoothGenConnected` (leaf candidate, published: Zariski's
  connectedness theorem, EGA III₁ 4.3, UNVERIFIED locators): smooth proper X over a presentation
  of 𝓞_L[1/f] with geometrically connected generic fibre is geometrically connected.
- Proved: `geometricallyConnected_of_geometricallyIntegral`, `hasGoodReduction_of_base` (base
  change of an abelian scheme along R → O compatible with the maps to K),
  `goodRedCofinite_of_neron : AbVarSpreadsOut → ProperSmoothGenConnected → GoodRedCofinite`
  (R = Localization.Away f; S = prime factors of absNorm (span {f}); `Ideal.absNorm_mem` gives
  N ∈ (f), N a unit of O_w, so f is a unit of O_w; φ = IsLocalization.Away.lift;
  `Grp.mkIso' gen` turns neron-lg's (G, gen, IsMonHom) into a Grp iso).
- part_final: `algFrobRed_of_neron`, `tateBridge35_of_neron`.
- Run 3: FrobPieces.lean exit 0, ~2 min 15 s, 99 axiom prints all standard, 0 sorryAx (VERIFIED,
  run3.txt). Pitfall: `RespectsIso @GeometricallyConnected` not found by instance search; give it
  as `MorphismProperty.IsStableUnderBaseChange.respectsIso` with the type annotated at Scheme.{0}.

## Merges (10:25)
- Merged origin/main (54cc2893, w43): conflict in ThirdParty/TauCeti/NOTICE (ring-class paragraph vs
  this task's entry), resolved keeping both; .fleet/alg-frob-red.md deleted as on main.
  diffcheck2 after merge: NOTE-ONLY 0, MOD-UNNOTED 0 (VERIFIED).
- Merged origin/wip/afr-absfrob (2ffcf322, finished): `AlgFrobRedRed.absFrob : AbsFrob` (Mathlib),
  `fExtendGen_of_nmp : PkgI2.NeronMappingAbelianScheme → FExtendGen`, `algFrobRed_of_nmp`.
  Its AfrAbsFrob.lean is up to date with its build.sh (cmp, VERIFIED).

## Combined form (VERIFIED, compiled)
- build_full.sh → FrobPiecesFull.lean = src_AfrAbsFrob.lean (cmp-identical to
  scratch/afr-absfrob/AfrAbsFrob.lean, which begins with a cmp-identical AlgFrobRed.lean) + Contrib
  import + part_good + part_neron + part_final + part_full.
- part_full: `algFrobRed_of_neron_nmp : AbVarSpreadsOut → ProperSmoothGenConnected → I2-Red →
  I2-NMP → FrobTrace.AlgFrobRed`, `algFrobRed_of_spread_nmp` (AbSchemeSpreadsOut, I2-Red, I2-NMP),
  `algFrobRed_of_goodRed_nmp` (GoodRedCofinite, I2-Red, I2-NMP), `tateBridge35_of_neron_nmp`,
  `tateBridge35_of_spread_nmp`.
- Run full-1: `lake env lean scratch/frob-pieces/FrobPiecesFull.lean` exit 0, ~3 min, 114 axiom
  prints, all [propext, Classical.choice, Quot.sound], 0 sorryAx (VERIFIED, run_full1.txt).

## Review (one model review, read-only, no human review; ~10:40)
- AbSchemeSpreadsOut: TRUE, non-vacuous (𝓞_L[1/N] = closure of a finite set; spreading out +
  Zariski). ProperSmoothGenConnected: TRUE, non-vacuous (f = 0 vacuous; R ≅ 𝓞_L[1/f] normal;
  f_*𝒪_X = 𝒪 and EGA III 4.3; fibres nonempty by open+closed+connected). goodRedCofinite_of_neron
  sound.
- Wording fixes applied to the two docstrings (ℤ[s] need not be normal; 𝒪_{Spec R}; flatness for
  torsion-freeness; nonempty fibres; Hartshorne III 11.3 is for projective morphisms, dropped).
- After the fixes: FrobPieces.lean run 3 exit 0, 99 prints standard, 0 sorryAx; FrobPiecesFull.lean
  run full-1 exit 0, 114 prints standard, 0 sorryAx (VERIFIED, rerun ~10:50).
