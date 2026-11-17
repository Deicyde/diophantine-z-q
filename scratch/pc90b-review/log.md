# pc90b-review log (head a8099a02, base 517e05cce)

## (7) Rename scope: VERIFIED
- git diff --stat 517e05cce a8099a02: 7 files (3 vendored AnthropicFLT, PoleS12/Leaves.lean, Hypotheses/PoleManuscript.lean,
  OneProof/Main.lean, removal of scratch/upstream/parity-frozen-4eaee875.tex). No Tau Ceti file, no file pinned by upstream
  (none of the 6 .lean files is in scratch/upstream/baseline-lean-files.txt).
- Mechanical check (scratch/pc90b-review/rename/): the base version with the exact token `divisorSum` (no word character on
  either side) replaced by `placeDivisorSum`, diffed with the head version. Differences: only the 4-line "Modified" header
  in each file plus a `-- [port] renamed` comment on the def line. Lemma names (`divisorSum_single`, `divisorSum_pointDivisor`,
  ...) unchanged, and no name collides with Tau Ceti's lemmas (`divisorSum_apply`, `divisorSum_eq_zero_iff`, ...).
- No other file in a8099a02 uses the bare token `divisorSum` except Tau Ceti's Sum.lean and DivisorPullback.lean, and
  GreenTao's unrelated `SmoothSieveCutoff.divisorSum`.

## (4) S12: VERIFIED
- git ls-tree -r a8099a02 | grep -i parity-frozen: empty. Blob hash of S12 (f319c4da) is not in the tree.
- Fixed-string grep of all 460 distinct non-comment S12 lines of >= 40 chars over the whole tree: one match, a 66-char
  generic phrase in ZInQKernel/Contrib/OneProof/PoleS12/Primes.lean (not touched by the five commits), starting
  "remainder theorem gives a reduced residue class, and Dirichlet's". No copy of S12.
- S12 is still in the history (commit 4b2595108, per pc90-review): history must be rewritten before any public merge.

## (5) Tau Ceti: VERIFIED with caveat
- The five commits touch no file under ZInQKernel/Contrib/TauCeti or ThirdParty (diff --stat empty).
- Pin 86b92544 is not an object in this repository or in any git repository under ~ (searched): not checkable as stated.
- The vendored headers name pins 5a01f5fe3621 / 97a5b23586f9 / 4d91513e4d30, all present in ~/tcrun/tc.
  tc_compare.py (header stripped, ZInQKernel.Contrib.TauCeti. -> TauCeti.): 1807 identical at 5a01f5fe, 45 identical at
  97a5b235, 47 differ (24 imports only, 23 also in code; all 47 carry a "Modified for the Z-in-Q kernel" note), 123 have no
  pin header (121 Backport/, MathlibBackport, Notice.lean). Lists: tc_compare.txt, tc_codediff.txt. All pre-existing.

## (6) Labels: FAIL
- Lemma54: labelled "printed leaf" (Leaves.lean:17), "printed form over genuine definitions" (Leaves.lean:81), and
  "the printed leaves Lemma 5.4" in Main.lean:12 and :137.
- KolyvaginThm1: bridge named (Leaves.lean:57-60: Shimura's construction and Faltings' isogeny theorem), but rated
  "printed leaf" (Leaves.lean:14, :52), not "consequence".
- Stale: KummerSelmerM still "textbook GLUE, not proved" at Leaves.lean:20 and :91.
- Early verdict committed: .fleet/pc90b-review-verdict.md (b5bf0a745).

## (2) forbidden tokens: VERIFIED
- sorry/admit/axiom/native_decide/implemented_by/extern/unsafe outside comments: 0 in each of the 6 changed .lean files;
  0 added lines with these tokens; 0 in KummerSelmerMProof.lean and PoleCompletenessFromRCGenuineFinal.lean.
