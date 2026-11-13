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
