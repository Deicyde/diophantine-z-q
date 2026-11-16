# gr14-narrow results log

Base: 43513d873 (leaf-fold25). Build: lean/.lake/build copied from ~/dzq-wt/pi0-prune (same lean/ tree 8094333d).

## Probe Live.lean (VERIFIED, compiled; output Live_out.txt)
Closure of `ZInQ.OneProof.frozenTarget`: 244,312 constants.
- Live R19 path: `heightRowsNo20_of8` (TailZ4) → `researchLeaves7_of_open8` → `OpenResearchLeaves7.r19` (TailX:105)
  → `researchLeaves5_of_open7` → `OpenResearchLeaves5.r19` (TailN:93) → `researchLeaves2_of_open5` →
  `OpenResearchLeaves2.r19` (TailE:6486) → `researchLeaves3_of_open2` → `ResearchLeaves3.r19` (TailD:76).
- Consumers of `ResearchLeaves3.r19`: `glueOutputs_of_leaves3` (via `transfer_core`, first conjunct only) and
  `reverseIsogeny_of_leaves3` (via `isogenyReverseExists_of_r19`, existence only), the latter used only by
  `gluePieces_of_open4` (TailK:308).
- Live bundles with field `gaudronRemondThm14`: OpenResearchLeaves8, 9, 14, 15, 16, 17, 18, 19, 20, 21, 22.
- Only non-copy use of the field: `heightRowsNo20_of8` (TailZ4:163, `r19_of_leaves`).

## Chain helper (GR14Narrow/Chain.lean) — compiles (lake env lean, no output)
- `GapGR.R19Fwd`, `r19Fwd_of_r19`, `transfer_core_fwd`, `natCast_hom`, `isIsogenyMor_of_comp_eq_mul`,
  `hom_ext_of_points` (copy of TailP's, + IsReduced instance line), `comp_eq_pow_of_isQuasiInverse`,
  `isogenyReverseExists_of_weil`, `reverseIsogeny_of_weil`.
- Finding: in TailB's import closure `IsReduced A.X.left` is not found by instance search (Y not determined);
  `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian A.X.hom` supplies it.

## Leaf helper + contributor file — compiled
- `lake build ZInQKernel.Contrib.OneProof.GR14Narrow.Leaf` OK; `lake build ZInQKernel.Contrib.OneProof.GR14Narrow`
  OK (12300 jobs; lake rebuilt the TYZGenus modules whose oleans/traces were missing in the copied build).
- `GapGR.GaudronRemondThm14Fwd`, `gaudronRemondThm14Fwd_of_field`, `r19Fwd_of_leaves`,
  `r19Fwd_of_leaves_of_field` (rfl), `isogenyReverseExists_of_milne`, `reverseIsogeny_of_milne`,
  `isogenyReverseExists_of_milne_eq_weil` (rfl), `gaudronRemondThm14Fwd_of_open`, `isogenyReverseExists_of_open`.
- Fold script scratch/gr14-narrow/apply_fold.py: --dry-run on the worktree: 27 edits in 20 files, every old text
  found exactly once.

## #discharges (discharges.txt) — VERIFIED
63 open hypotheses, 1822 theorems checked, 7 discharge one (all earlier contributions); no GapGR theorem
discharges a field (expected: narrowing).

## FoldCheck.lean — compiled
(a) transfer_core_fwd ∘ r19Fwd_of_r19 = transfer_core (rfl); (b) gluePieces_of_open4 with the new reverseIsogeny
term; (c) heightRowsNo20_of8 with R19Fwd. All #print axioms: [propext, Classical.choice, Quot.sound].

## Full fold build — VERIFIED
apply_fold.py on a reflink copy ~/gr14-foldtest (outside the repo, .git renamed so no git ops), then
`lake build +ZInQKernel.OneProof.Main`: Build completed successfully (12995 jobs, ~14 min);
frozenTarget axioms [propext, Classical.choice, Quot.sound]. Post-fold probe (PostFold_out.txt): old
GaudronRemondThm14 / R19_GaudronRemond / isogenyReverseExists_of_r19 / reverseIsogeny_of_leaves3 absent from the
live closure (244,317 constants). fold.patch = unified diff (26 hunks, git apply --check OK at base).
Note: ~/gr14-foldtest (~21 GB apparent, reflinked) is left in place (no rm -rf allowed).
