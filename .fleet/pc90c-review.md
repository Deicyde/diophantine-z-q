# pc90c-review: PR #90 head a04588b4

Report: `docs/research/pc90c-review.md`; log `scratch/pc90c-review/log.md`.

**Verdict: the Lean at a04588b4 is clean. The labels still fail. A merge onto be73b91c5 conflicts in one hunk; once
resolved, it builds.**

* (1) PASS. The build of OneProof.Main, MainGreenTao, every PoleS12 module, every PoleCompleteness* module and
  PoleManuscript succeeds (16180 jobs). `frozenTarget`, the MainGreenTao headline, `PoleS12.kummerSelmerM` and
  `poleCompleteness_of_restrictedConverseGenuine_final` use only propext, Classical.choice and Quot.sound. No
  sorry/admit/axiom occurs in the PR's ZInQKernel files. The only hits are 2 `sorry` in `scratch/pc-from-rc/T3.lean`,
  which is not built.
* (2) PASS. The merge a04588b4f keeps main's Leaves60, open79, TailZ86 and the ss-faltings/d2a6b docs, plus the PR's
  hRC, h54, hB, hK and its import. Nothing was dropped. Signature: Leaves60 → Textbook18 → Added27 → RCGenuine →
  Lemma54 → BCDTThmA → KolyvaginThm1 → FrozenTarget.
* (3) FAIL. All three label fixes are still missing (Lemma54 "printed leaf", KolyvaginThm1 "printed leaf",
  KummerSelmerM "not proved"). The affected places are Leaves.lean:7, 14-15, 17, 20, 52, 57-58, 81, 85-86 and 91,
  Main.lean:12-13 and 155-157, and PoleCompletenessFromRCGenuineFinal.lean:15 and 27. The report gives the exact
  replacement text for each. They are docstring edits only.
* (4) `git merge-tree be73b91c5 a04588b4` conflicts in `OneProof/Main.lean` only, in the frozenTarget signature (fold-c8's
  Leaves61/Added28/open80 against the PR's hRC/h54/hB/hK). Resolved with both, the merge builds (16495 jobs) with standard
  axioms. Resulting signature: Leaves61 → Textbook18 → Added28 → RCGenuine → Lemma54 → BCDTThmA → KolyvaginThm1 →
  FrozenTarget. The temporary worktree has been removed.
* Still open: S12 is in the PR's history (4b2595108), so squash before merging. origin/main has moved on to dafd6c7c8,
  which was not checked.
