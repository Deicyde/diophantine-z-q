# r16-thm1b results log (round 3 of r16-shimura73)

## Setup (13:08)
- Branch wip/r16-shimura73 at e7ac05a33 (fork main f3402e89 merged; top bundle OpenResearchLeaves57 in TailZ83,
  with fields heckeJ1DS and afShimura). VERIFIED (grep).
- Merge check: `lake build ZInQKernel.Contrib.OneProof.R16Thm1` started 13:09 (rebuilds the merged kernel).

## Drafts (13:20)
- ZInQKernel/Contrib/OneProof/R16Thm1b.lean: ShimuraThm1Af (one row: ShimuraClauses ∧ IsAfQuotient ∧ uniqueness
  up to nu-compatible iso among ShimuraClauses-triples; K_f finite), afShimura_of_thm1Af, r16CoreY_of_thm1Af.
- scratch/r16-thm1b/autofold.json: heckeJ1DS by heckeJ1DS_of_bSh (leaf bShStandardModel, flag updated per (d)),
  afShimura by afShimura_of_thm1Af (leaf shimuraThm1Af, consequence, flagged steps). shimuraQuotientIsAf dropped.

## Merge check (VERIFIED, 13:23)
- `lake build ZInQKernel.Contrib.OneProof.R16Thm1` on the merged tree (11362 jobs): success; R16ShimuraLi,
  R16CoreYDS965, R16Thm1 build (linter warnings only). Nothing broken by the merge; no fix needed.

## Lean (VERIFIED, 13:25)
- R16Thm1.lean docstrings edited (misprint location per ruling (c); xiSq a theorem step per (b); multiplicity one
  cited to Shimura 1973 p. 527 instead of DS 6.6.4 / Shimura 1971 Thm 7.14). Rebuilt: success.
- `lake build ZInQKernel.Contrib.OneProof.R16Thm1b`: success, no warnings in R16Thm1b.
- Axioms (Axioms-output.txt): afShimura_of_thm1Af, r16CoreY_of_thm1Af, heckeJ1DS_of_bSh, afShimura_of_shimura73,
  euler_of_shimura73_li, r16CoreY_of_shimura_li: [propext, Classical.choice, Quot.sound].

## Fold (VERIFIED, 13:30)
- Dry run (worktree; --dry-run writes nothing): `strict count: 5/24 on 29 -> 5/24 on 29; strictest 5/24 -> 5/24`.
  Count-neutral (round 2's two-row version was +1). No --allow-rise. Output FoldDryRun.lean.txt (stdout: count
  line + module; Main.lean after the fold in autofold-dryrun-err.txt). New top: sixContactMin_of_open77,
  OpenResearchLeaves58, TailZ84.
- Real autofold on a git-archive copy (/tmp/r16b-fold.neMk; worktree untouched): kinds-diff.txt = -afShimura,
  -heckeJ1DS (both consequence GLUE/GLUE), +bShStandardModel, +shimuraThm1Af (both consequence GLUE/GLUE,
  flag_class pending-review, rated_by "r16-thm1b; pending review", area elliotglazer/diophantine-z-q#37).
  render_open --check there: only "kinds.tsv does not classify afShimura, heckeJ1DS / rows no longer open"
  (OpenStatements not regenerated; needs the Lean build).

## Fold checks (VERIFIED, 14:12)
- lake build ZInQKernel.OneProof.Main + Discharges on the merged tree: success (15987 jobs; frozenTarget standard).
- FoldCheck.lean compiles; sixContactMin_of_open77: [propext, Classical.choice, Quot.sound].
- #discharges: 30 open hypotheses, 11497 theorems checked, 18 discharge one; afShimura by
  R16Thm1b.afShimura_of_thm1Af (still assumes ShimuraThm1Af), heckeJ1DS by R16Thm1.heckeJ1DS_of_bSh (still assumes
  BShStandardModel); standard axioms.
## Report docs/research/r16-thm1b.md complete.
