# yu-prune (2026-11-15)

**Result: `ZInQ.OneProof.frozenTarget` no longer assumes `yuThm11` (Chia-Fu Yu 2013, Thm 1.1). Nothing was added in
its place.** (VERIFIED)
* H fields: 58 → 57.
* Strict count (kinds.tsv, H rows): 45/13 → 44/13. Strictest: 44/14 → 43/14.
* `#discharges` open hypotheses: 65 → 64.

**How.** The chain used Yu's theorem only at four places. In each, Yu's statement was needed only at
`B = (2, −3)`, for QM by the maximal order, over a field algebraic over ℚ. gt-qm had already proved that case as
`HDec.QMLattice.YuB6Alg`, from three textbook leaves the bundle keeps.
* The four application theorems and about 20 pass-through consumers now take `hYu : YuB6Alg` in place of
  `PkgI3.QMDichotomyYu`, which is a weaker hypothesis.
* The definition `YuB6Alg` moved verbatim from QMLattice.lean into TailA; its hashes are unchanged.
* `hYu` is threaded through `sixContactMin_of_open4` … `_open23`. `_open24` (TailZ30) supplies it as
  `yuB6Alg_of' t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed`.
* PruneScan then found only `yuThm11` unused. The prune deleted:
  * 10 fields (`yuThm11` in OpenTextbookLeaves7–11, `t27` in TextbookLeaves and OpenTextbookLeaves2/3/4/6);
  * the 11 assignments into them;
  * 5 off-chain dead readers;
  * the temporary bridge helper.

**What compiles** (VERIFIED):
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`;
* `frozenTarget` axioms = propext, Classical.choice, Quot.sound;
* PruneScan 0 unused of 57.

**Checks** (VERIFIED):
* DumpCompact/cmp_hashes against a base worktree: 17 removed, 2 new, 198 changed, all classified.
* About 35 TailA–TailH constants changed value only, through auxiliary `_proof_N` sharing; CanonHash.lean shows they
  are equal modulo those names.
* DischargesTest: same discharges and controls.
* OpenStatements and render_open regenerated the docs; `--check` passes.

**Notes**
* The base 688b450d did not build at TailZ32 (a vendored StacksCore import clash). I merged origin/wip/leaf-fold19
  (c2ad4181), which carries the fix.
* docs/one-proof/frontier-crosswalk.tsv still lists `H-128 yuThm11`. That file is not mine to edit.
* A detached worktree ~/dzq-wt/yu-prune-base (the base build used for the hash comparison) was left in place.
  Remove it with `git worktree remove`.

Report: docs/research/yu-prune.md. Log and tools: scratch/yu-prune/.
