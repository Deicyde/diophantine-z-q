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
