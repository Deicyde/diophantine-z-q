# Replaying fold34-semiab on a later head

The contribution files are separate from the fold. Commits of wip/fold34-semiab:

* `b79455c67`, `58ea879cc`: merges of wip/height-fix (49e6d97d, which brings height-dict) and wip/semiab-descend
  (6a6de248). They add only new files: `ZInQKernel/Contrib/OneProof/{HeightDictionary,HeightDictionary/*,
  PrintedStableHeight,SemiAbelianDescendsPerfect}.lean`, plus notes and scratch.
* `274a30239`: hygiene. Five scratch files that redeclare HDec.HSyn bundles are renamed `.lean.txt`.
* `eabf87ab7`: the fold. It is generated: `TailZ56.lean`, Main.lean, kinds.tsv and claims.tsv come from autofold. The
  one exception is a hand-written docstring paragraph in Main.
* `c4312786b`: the regenerated docs and the check outputs.

On a head H that has further autofolds:

1. Merge wip/height-fix and wip/semiab-descend into H, or merge wip/fold34-semiab and drop its fold commit. Then
   apply the hygiene renames.
2. `lake build ZInQKernel.Contrib.OneProof.SemiAbelianDescendsPerfect`. Besides Mathlib and `Contrib/HeightBC/OmegaBC`, its
   imports are `TailZ4`, `TailZ19`, `RaynaudSemistableOr` (dict-models) and `GeomConnOfRationalPoint`, so it does not depend on the head's top.
3. Pick the spec:
   * If `bostLowerBound` and `gaudronRemondThm14` are still fields of the head's bundles, use
     `python3 scripts/one_proof/autofold.py scratch/fold34-semiab/autofold.json` (first with `--dry-run`).
     * The proofs use `{t}.mumfordTorsionAlgClosed`. If that textbook field has been discharged on H, replace it in
       the spec by its proof term.
     * They also use `_root_.uniformizationLeafAll_proof` (`Contrib/OneProof/UniformizationLeafAll.lean`).
   * If height-fix alone was folded first (`semiAbelianDescendsPerfect` is a field), use
     `scratch/fold34-semiab/autofold-after-height-fix.json`.
   * Expected dry run from the base c0f3d085: `strict count: 11/18 on 29 -> 14/16 on 30`. On any head, the strict
     and strictest GLUE counts each drop by 2, one field is added, and nothing rises.
4. Optionally add the Main docstring paragraph (see `eabf87ab7`).
5. Run the checks:
   * `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`;
   * `scratch/fold34-semiab/checks.sh TAG`, which runs the hash dump, the closure, OpenStatements, DischargesTest and
     `#discharges`;
   * `hashdiff.py` against a dump of H;
   * `render_open.py` then `--check`;
   * `frontier_crosswalk.py` then `--check`;
   * the autoform check.

Do not fold the optional javanpeykar/pazuki rows. `autofold-all4-honest.json` (rated honestly) does not change the
count; see log step 4.
