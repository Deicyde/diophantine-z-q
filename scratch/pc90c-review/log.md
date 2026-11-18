# pc90c-review log (head a04588b4f, worktree wip/pc90c-review = a04588b4f)

- Parents of a04588b4f: ^1 = a8099a02a (PR), ^2 = b9b854867 (fork main); merge base 67950e829. VERIFIED (git).
- `git show --remerge-diff a04588b4f --stat`: only ZInQKernel/OneProof/Main.lean differs from the auto-merge; one conflict
  hunk (frozenTarget signature + body). Resolution = PR's hRC/h54/hB/hK + main's OpenResearchLeaves60 /
  sixContactMin_of_open79. VERIFIED.
- Main.lean vs PR parent: import TailZ83→TailZ86 (main's), ss-faltings + d2a6b doc paragraphs (main's), Leaves57→60,
  open76→open79. Main.lean vs main parent: import of PoleCompletenessFromRCGenuineFinal, docstrings, hPC→hRC,h54,hB,hK.
  Nothing else dropped. VERIFIED (git diff).
- Labels at a04588b4f (Leaves.lean / Main.lean unchanged by the merge except Main lines shifted): Leaves.lean:7, :14, :17,
  :20, :52, :81-86, :91; Main.lean:12, :156. Also PoleCompletenessFromRCGenuineFinal.lean:15, :27. VERIFIED (read).
- merge-tree origin/main(be73b91c5) a04588b4f: exit 1, tree d065e84f3, CONFLICT (content) in ZInQKernel/OneProof/Main.lean
  only, one hunk at the frozenTarget signature (main: Leaves61/Added28/open80/hPC; PR: Leaves60/Added27/open79/hRC,h54,hB,hK).
  Imports auto-merged (TailZ87 + PoleCompletenessFromRCGenuineFinal). VERIFIED.
- (1) `lake build` of 25 targets (OneProof.Main, MainGreenTao, all 13 PoleS12/*.lean incl. GoodF, the 9
  PoleCompleteness*.lean, Hypotheses.PoleManuscript; list in build-targets.txt): **Build completed successfully (16180
  jobs)**, EXIT 0, 0 errors. VERIFIED (build1.log, 18:35).
- Axioms.lean → Axioms-output.txt: frozenTarget, MainGreenTao headline, PoleS12.kummerSelmerM,
  poleCompleteness_of_restrictedConverseGenuine_final: [propext, Classical.choice, Quot.sound]. VERIFIED.
- frozenTarget at a04588b4f (#check): OpenResearchLeaves60 → OpenTextbookLeaves18 → OpenAddedLeaves27 →
  RestrictedConverseGenuine → Lemma54 → BCDTThmA → KolyvaginThm1 → FrozenTarget. VERIFIED.
- Token grep (sorry|admit|axiom|native_decide|implemented_by|extern|unsafe, whole word) over the 64 .lean files the PR
  changes vs b9b854867: no hit under ZInQKernel/; 2 hits in scratch/pc-from-rc/T3.lean:181-182 (`sorry`, a scratch file,
  not built, not imported). VERIFIED.
