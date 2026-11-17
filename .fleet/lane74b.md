# lane74b (2026-11-17): lane74 follow-ups, checklist items 1, 3, 4, 5, 7 and the H-reach/waiver part of 2

**Result.** Every item is done or answered, and no statement was changed or added (no on-the-spot statements).
Each item is its own commit on `wip/lane74b`, based on f558b164. Report: `docs/research/lane74b.md`; log:
`scratch/lane74b/log.md`.

* **1.** The current Main already has the shape autofold.py:68 needs, and it keeps TailZ79, MainGreenTao and
  DeRhamRange. `autofold.py` now parses the Main it writes and stops on a bad switch. `--dry-run` prints the switched
  Main on stderr. The gate for the lead is `scratch/lane74/gate.sh`: a no-op dry run, a tree-unchanged check, and a
  compile of the fold module with standard axioms. On this branch it prints GATE=ok.
* **2 (H reach and waiver).** Nothing H reaches was cut, so no file was moved. H's import closure reaches 58 RouteK
  modules, all present and built, including Slots.Theta → Parity → Pole and LPrefix → ConstantsProperties → Pole.
  The hash dump covers every `ZInQKernel` constant, from be9a6ba4a to this branch:
  * 20 changed: the polePoly/poleT1/poleT2/abscissa_val_even set, `frozenTarget`, and 3 equation lemmas whose module
    field moved;
  * OneProof/H byte-identical (17 686 records).

  Waiver: `scratch/lane74/HASH-WAIVER.md`.
* **3.** `Pole.lean` is reverted byte for byte, docstrings with body, to b570b14ee. No constant changed.
  Finding: upstream's contract pins Pole.lean at the Route K blob d61c9c41.
* **4.** STATUS.md's recipe now names `+OneProof.Main`, frozenTarget's axiom check and print_axioms' 463
  declarations. print_axioms has 0 nonstandard declarations and none from the cone.
* **5.** 59 blueprint pages are marked (listed in the report): 51 are unformalized with a removal note, 8 keep the
  names that still exist. `autoform check --lean-root .` and `render --require-declarations` pass.
* **7.** 28 TYZ/GZ/CR₃-named modules and the 58 RouteK modules still compile through H's imports, among them
  `Literature.GrossZagier`. The report lists them, with docs wording for #81. Re-homing is not cheap: H's T5 glue
  uses 62 constants of TYZGenus's Shimura/CM development, and TYZGenus.RingClass imports Route K. The cut is a file
  split (recipe in the report).

**Compiles / checks (VERIFIED):**
* `lake build ZInQKernel +OneProof.Main +OneProof.Discharges`;
* frozenTarget axioms standard; print_axioms 463/0;
* render_open --check ok (30 open); crosswalk --check ok;
* autoform check (both forms) ok; DischargesTest EXIT 0.

**Not run:** CONTRIB-BUILD, AllContrib, Leaves.lean, site check. `scratch/lane74b/PoleRefs.lean` was stopped after
10 min and is unchecked (not needed).

**Lead:**
* Run `gate.sh` in the chain.
* Accept or reject the waiver.
* Upstream needs a contract change for Pole.lean.
* contrib-kit's saved DischargesTest output is stale.
* `~/l74b-base`, a detached base worktree used for the hash dump, can be removed.
