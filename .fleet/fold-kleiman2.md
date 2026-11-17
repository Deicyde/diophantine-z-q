# fold-kleiman2 (fleet note)

**Verdict: folded.** On wip/leaf-fold33b 75d94fe7, the added field `kleimanPicZeroProper` (`PicFix.KleimanPicZeroProper`,
GLUE) is replaced by kleiman-section2's leaf `kleimanPicZeroProper954` (`KleimanSection2.KleimanPicZeroProper954`,
Kleiman 9.5.4 under its own hypotheses). The branch merges wip/kleiman-section2 7591fc3b and adds a copy reroute,
`ZInQKernel/OneProof/H/TailZ68.lean`, ending in `sixContactMin_of_open61` with
`OpenAddedLeaves26 = {picRepresentableAbVar, kleimanPicZeroProper954}`. Main is patched. The new leaf is weaker than
the field, so autofold does not apply. On the current top the field is read only as `PicZeroAbVar0`, in two places:
the `25→22PZ` conversion and fold34-ht's `hodgeTateDecompAbVar_of_open` in `EichlerBoundCopy`. `TailZ68` copies 14
declarations as `X_k954`; no existing declaration is changed.

**Compiles (VERIFIED).**
- Build `+Main +Discharges` plus the new modules completed (16076 jobs).
- `frozenTarget` uses only the standard axioms.
- Hash guard: only `frozenTarget` changed; 26 constants were added, all in `TailZ68`.
- Closure: the old Prop and `sorryAx` are absent.
- `OpenStatements` gives 39. `render_open` gives 34 H, strictest 11/23, 5 others, and `--check` is ok.
- The crosswalk `--check` is ok, `DischargesTest` reran with no error, and the autoform check is ok.

**Count.** Neutral: one GLUE field out and one pending-review leaf in. It becomes −1 GLUE once a reviewer rates
`kleimanPicZeroProper954` LEAF. `#discharges` cannot show the old field discharged, because the leaf is weaker. The
brief anticipated this.

**Replay.** Run `python3 scratch/fold-kleiman2/gen/gen.py --write`; `scratch/fold-kleiman2/gen/README.md` has the
instructions. The kinds row is in `scratch/fold-kleiman2/kinds-row.tsv`; also drop the claims row
`kleimanPicZeroProper`.

**Remains.** A review of the new leaf. A `locators.md` row for Kleiman 9.5.4 (numbering UNVERIFIED on the host). The
SPECULATIVE question of whether `picRepresentableAbVar` over all `K`-schemes exceeds Kleiman 9.4.8, which is stated
over locally Noetherian test schemes. Report: `docs/research/fold-kleiman2.md`.
