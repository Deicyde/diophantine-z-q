# lane74b results log

Base: wip/lane74-int f558b164 (frozenTarget (r : OpenResearchLeaves53) (t : OpenTextbookLeaves18)
(l : OpenAddedLeaves27) (hPC), via sixContactMin_of_open72, Main imports TailZ79, MainGreenTao, DeRhamRange).
Warm build copied (reflink) from ~/dzq-wt/lane74-int/.lake/build and lean/.lake/build (built at f558b164).
`lake build ZInQKernel +OneProof.Main +OneProof.Discharges`: OK, 16053 jobs (24 rebuilt), 1m45. VERIFIED.

## Item 5: blueprint (commit "lane74b item 5")

- Base `autoform check blueprint --lean-root .` (autoform-bot@46b46d6d, uvx --offline): EXIT 1, 199 errors in 59
  articles (scratch/lane74b/autoform-leanroot-base.txt). 10 of them (route-k/realization, names in namespace
  `ZInQ.RouteK.Slots`, which is also a structure) carry an extra "is a structure" message; all 199 names are
  declarations deleted by lane74 #77. VERIFIED.
- scratch/lane74b/blueprint_mark.py: per article, drop the missing names from `lean:`; if none remains (51 articles)
  drop `lean:`, `statement:`, `proof:` (page becomes unformalized); add a one-line note after the title naming the
  removal (#77), the tag `route-k-final` and #81. 8 articles keep some names (partial). Articles touched:
  scratch/lane74b/blueprint-touched.txt (59: main 10, rank 38, rank-5b 7, route-k 4). No article deleted, no link changed.
- After: `autoform check blueprint` EXIT 0; `--lean-root .` EXIT 0 (776 articles, 645 fully proved, 2328 names
  resolved); `autoform render blueprint --lean-root . --require-declarations` EXIT 0 (175 pages, 701 nodes).
  VERIFIED (scratch/lane74b/autoform-check*.txt, autoform-render.txt).

## Item 1: autofold + gate

- Current Main (f558b164) already has the shape autofold.py:68 needs: `theorem _root_.ZInQ.OneProof.frozenTarget`,
  binders, `(hPC : ZInQ.PoleCompleteness) :` newline `ZInQ.FrozenTarget`, the call
  `(HDec.HSyn.sixContactMin_of_open72 r t l) hPC`, imports TailZ79 + MainGreenTao + DeRhamRange (no binder comments).
  `main_state()` parses it: binders r/t/l, top sixContactMin_of_open72, last module TailZ79. VERIFIED (python).
- autofold.py change: `main_state(s=None)` parses a text too (docstring states the required shape); after switching
  Main, autofold re-parses the switched text and dies unless the top theorem is `sixContactMin_of_open{N+1}`, the
  TailZ import is the new module, the other imports (MainGreenTao, DeRhamRange) are unchanged and the binder names /
  bundles are the old ones with the bumped generations. Before, a failed `str.replace` would have written an
  unchanged or half-switched Main silently. `--dry-run` stdout unchanged (count line + module); the switched Main
  goes to stderr.
- Dry runs: no-op spec (scratch/lane74b/gate-noop-spec.json, no discharge): EXIT 0, prints
  `sixContactMin_of_open73 r t l := sixContactMin_of_open72 r t l` over TailZ79; switched Main imports TailZ80,
  MainGreenTao, DeRhamRange, calls `(HDec.HSyn.sixContactMin_of_open73 r t l) hPC`. One-field spec (discharge
  `picRepresentableAbVar` of OpenAddedLeaves27, proof a dummy name, not compiled): EXIT 0, OpenAddedLeaves28,
  switched Main binder `(l : HDec.HSyn.OpenAddedLeaves28)`, `hPC` kept. Tree unchanged after both. VERIFIED.
- Gate script for the lead: scratch/lane74/gate.sh (the chain scripts are outside the repository): no-op dry run,
  tree-unchanged check, compile of the printed fold module, axioms of sixContactMin_of_open73 standard; prints GATE=ok.

## Item 3: Pole.lean

- Pole.lean at f558b164 already had lane74's manuscript body with rewritten docstrings (no "x + ℓ" / "PC is a theorem
  from CR₃" left; those were in the Route K version d61c9c41, which is also the hash upstream's contract pins at
  9c7b60ef). Item 3 done literally: Pole.lean reverted byte for byte, docstrings with body, to b570b14ee
  (= the kernel skeleton cb193ab1b's file, blob 842f08ae). Only docstrings differ from f558b164 (no declaration
  changes). VERIFIED (git hash-object = 842f08ae).
- Upstream contract: the pinned blob of ZInQKernel/Hypotheses/Pole.lean at 9c7b60ef is d61c9c41 (Route K polynomial);
  any manuscript-polynomial Pole.lean differs from it, so the file needs a contract waiver upstream either way
  (FINDING for the lead).
- Remaining Route K wording about PC outside Pole*.lean: ZInQKernel/Hypotheses/CertifiedRank.lean:10 names
  `ZInQ.poleCompleteness_of_certifiedRank` (deleted); CertifiedRank.lean is one of the kept H-reach files (item 7).
- Build after the revert: `lake build ZInQKernel +OneProof.Main +OneProof.Discharges` OK, 16053 jobs (first run stopped
  by the harness's 10-min background limit after ~150 modules, rerun completed: 227 rebuilt, 19m39); frozenTarget
  axioms [propext, Classical.choice, Quot.sound]. VERIFIED (scratch/lane74b/build1b.txt).
- Hash dump f558b164 vs lane74b-after (every ZInQKernel constant of ZInQKernel + OneProof.Main): 179119 = 179119,
  0 changed, 0 removed, 0 added (docstring-only revert). VERIFIED (scratch/lane74b/hashcmp-f558-after.txt).

## Item 4: print_axioms / STATUS recipe

- scripts/print_axioms.lean already lane74's (463 #print lines, headline `..._of_sixContactMin_poleCompleteness` first).
  Run after the rebuild: EXIT 0, 463 "depends on axioms", ~/dzq-runs/axcheck.py: decls 463, nonstandard 0, no sorry.
  Defining modules (from the hash dump): 462 in ZInQKernel modules + Submission.green_tao (ThirdParty); none in RouteK,
  TYZ*, GZ*, Hecke*, CR3*, CertifiedRank, PSide, GaussFE or the 79 kept modules
  (scratch/lane74b/print_axioms-modules.txt). VERIFIED.
- Added a header note (comment only): frozenTarget is checked by the `+ZInQKernel.OneProof.Main` build (the file imports
  only ZInQKernel, and the chain runs it before the OneProof build, so no import was added).
- STATUS.md recipe ("To build and check"): build `ZInQKernel +ZInQKernel.OneProof.Main`, frozenTarget's axioms printed by
  the build, print_axioms' 463 declarations described with the new headline. The 5e235a40 verification paragraph
  ("542 declarations") is a dated record and was left. check_target.py: ok. VERIFIED.

## Item 2 (part): H reach and hash waiver

- reach.py / paths.py over the import graph (lane74's graph.py): H closure (OneProof/H/**, HDecomp/**, OneProof/Main)
  2131 modules, 58 RouteK (scratch/lane74b/h-reach-routek.txt); all files exist and build. Every path enters through
  OneProof/H/TailZ34 -> Contrib/OneProof/RayClassShimura -> Contrib/TYZGenus/ShimuraModFn. LPrefix ->
  ConstantsProperties -> Hypotheses/Pole and RouteK.Slots.Theta -> Certificate.Parity -> Pole intact. VERIFIED.
- Uses.lean: frozenTarget closure 292948 constants; from the 79 kept modules (scratch/lane74b/kept-mods.txt = lane74's
  78 + RouteK.Selmer.CharSum) only TYZGenus.Shimura.sqrt_mul_self_C, TYZGenus.X0.instDecidableEqComplex_zInQKernel,
  plus 12 RouteK.Selmer.CharSum constants via Density.CharSum. VERIFIED (compiled, 3m22).
- Uses2.lean: all constants of the 86 H-reach modules that import a kept module (sees-kept.txt): 7304 scanned, 180
  (module, kept constant) pairs; H-side (outside the HeckeAll/GaussFE/PSide cone) 62 kept constants from
  TYZGenus.{CM,RingClass,ShimuraField,ShimuraMain,ShimuraModFn,ShimuraRecip,ShimuraZn,X0}, TYZDecomp.CurveA,
  RouteK.Rank5b.Sec3.RedeiStatement (QNeg x3), RouteK.Selmer.CharSum; referenced by RingClassLattice (55),
  RayClassShimura (7), DeligneComponentsY3Used, GR56Lattice, WeberField (1 each), Density.CharSum (6). VERIFIED.
- No file moved (nothing cut; moving would rename private constants and not let anything go).
- HashDump.lean (DumpCompact record for every ZInQKernel constant, env ZInQKernel + OneProof.Main) at be9a6ba4a (detached
  worktree ~/l74b-base, build reflinked from ~/dzq-check2, lake build replayed 16314 jobs, nothing rebuilt): 188726;
  f558b164: 179119; lane74b after rebuild: 179119. cmp_hashes_full.py: base->f558 changed 20 (list in HASH-WAIVER.md),
  only-before 9613 (8538 deleted files, 1055 unimported Tau Ceti files, 20 in surviving modules), only-after 6;
  f558->after 0/0/0; OneProof.H 17686 records byte-identical base vs f558. VERIFIED.
- PoleRefs.lean (pole-module constants mentioned by OneProof constants): killed after 10.5 min without output; not
  needed (OneProof/H records unchanged). UNCHECKED.
- Waiver: scratch/lane74/HASH-WAIVER.md.

## Checks after the last Lean change

- gate.sh: AUTOFOLD-DRYRUN-EXIT=0, TREE-UNCHANGED=yes, GATEFOLD-EXIT=0, GATEFOLD-AXIOMS=standard, GATE=ok. VERIFIED.
- render_open.py --check: ok, 30 open hypotheses, 4 generated files up to date. frontier_crosswalk.py --check: ok.
- DischargesTest.lean (scratch/contrib-kit): EXIT 0, "#discharges: 30 open hypotheses, 11256 theorems checked, 16
  discharge one" (output scratch/lane74b/DischargesTest-output.txt). Its controls t1 (nvLocalInertia) and t3
  (cartierSmooth) name fields no longer open, so they print nothing; the file's saved output in scratch/contrib-kit is
  stale (owner: contrib-kit). VERIFIED.
