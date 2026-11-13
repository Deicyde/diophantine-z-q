# g8-object results log

## Step 1 (2026-11-13 06:30-06:50 PST): the object and the G15 restatement (Dev.lean)
- Kernel modules built: `lake build` of C2, LadicCond, Different, ModCurves.Glue, RhoCont, TateBC,
  C10.Link, QM.Leaves, WP3, ModCurves.Defs, T32a (2m15s), then JHeight/Height/Constants (builds the
  upstream `lean/` helpers needed by `Hypotheses.Height`).
- `scratch/g8-object/build_dev.sh` assembles `Dev.lean` = `scratch/g15-ram/G15Ram.lean` verbatim
  (+ imports `Descent.ProjRep`, `I3Linalg.C2` after its own) + verbatim g0-mod-galois definitions
  (`part_galois.lean` L27-152: `resQ` … `G8Out`; `part_matrix.lean` L11-21: `BurnsideAbsIrred`)
  + `part_obj.lean` (new, namespace `G8Object`).
- New (part_obj.lean): `DescData A ℓ` (G7Out data + `dim = 4`), `DescData.ofG7Out` (from T26),
  `DescData.rho`, `basis`, `rW`, `m`, **`DescData.r : GaloisRep ℓ 2`** (the object), `DescData.e`,
  `intertwines`, `rho_resQ`, `g8Out` (full `G0Galois.G8Out` from C2's leaves + Burnside);
  `mat_eq_scalar_of_intertwines`, `toHom_eq_one_of_intertwines`, `g11_of_intertwines`;
  `TmWild`, `BetaUpper`, `BetaTame`, `SmallPrimeG`, `LargePrimeG`, `LocalDataG` (on `(Tm, a, β)`);
  `twistShape_of_tmWild`, `localData_of_intertwines`; `ModObj`, `ModObj.toModData`,
  `g15RamG_obj`, `g15RamG_of_intertwines`.
- Compile (VERIFIED): `lake env lean scratch/g8-object/Dev.lean` exit 0, 0 errors, no sorry,
  45 s; `#print axioms` = [propext, Classical.choice, Quot.sound] for `DescData.intertwines`,
  `DescData.g8Out`, `mat_eq_scalar_of_intertwines`, `g11_of_intertwines`,
  `localData_of_intertwines`, `g15RamG_obj`, `g15RamG_of_intertwines` (plus g15-ram's 13).
