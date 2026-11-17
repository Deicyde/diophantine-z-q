# lane74 results log

Base: wip/leaf-fold33b 74395dcf0. Build tree copied (reflink) from ~/dzq-check2 at 74395dcf (warm).
Issues #74/#76-#79 not readable (gh: connection reset; no network). Worked from the brief.

## #77 (commit 1)

- Tag: `git tag route-k-final bf691da2236b494bb429caabc2f907d4ea428c4d` (SHA from
  `grep LANDED ~/dzq-runs/landed.txt | tail -1 | cut -d' ' -f1`). Local tag created; push failed
  (CONNECT tunnel 403), not retried; command in scratch/lane74/TAG.md. VERIFIED.
- Import graph: scratch/lane74/graph.py (imports of all 7145 tracked ZInQKernel .lean files) and
  delset.py (named set + forced closure). H-reach = transitive imports of OneProof/H/** and
  HDecomp/** (1790 modules).
- Named set (RouteK/**, Contrib/{TYZChain,TYZDecomp,TYZGenus,GZDecomp,GZStatements,GZTheta,HeckeFE},
  MainLiterature, Hypotheses/{CertifiedRank,CR3Literature,TYZInputs}, OneProof/{TYZSplit,TopChain},
  the Contrib/OneProof files in the import closure of OneProof/Main's TYZ/GZ imports and not in
  H-reach) plus forced importers (GaussFE/Headline, PSide/* except TYZInputsIff, three NonVacuous /
  OptimalUnique files, TYZGenusFold/QI, TYZSquareOddness, TYZThm21PairsOne): 298 modules.
- FINDING (importer check): 78 of them are in H-reach and were NOT deleted
  (scratch/lane74/kept-h-reach.txt, 27831 lines). Single entry point:
  OneProof/H/TailZ34 imports Contrib/OneProof/RayClassShimura, which imports
  Contrib/TYZGenus/ShimuraModFn (RingClassLattice, also in H-reach, imports TYZGenus.ShimuraModFn and
  ShimuraMain). From there: TYZGenus.{ShimuraField,ShimuraZn,ShimuraRecip,RingClassBridge,Package}
  -> TYZDecomp.Leaves -> HeckeAll.Provider -> {GaussFE.FunctionalEquation5, HeckeAll.Continuation}
  -> HeckeFE.Basic -> {RouteK.Rank.LFunctionCd, Hypotheses.CR3Literature}; TYZDecomp.Leaves ->
  PSide.TYZInputsIff -> RouteK.PropN; TYZGenus.RingClass -> RouteK.Rank5b.Sec3.RedeiStatement,
  RouteK.Redei.FourRank, Hypotheses.TYZInputs; and RouteK.{Slots,System,Selmer,Assembly.Realize,...}.
  VERIFIED (BFS path printed by scratch tool).
- FINDING: Density/CharSum (Proposition D, used by the headline through MainGreenTao) imports
  RouteK/Selmer/CharSum (Mathlib-only character sums). Kept in place (not deleted).
- Deleted: 220 files, 70475 lines (scratch/lane74/deleted-files.txt). VERIFIED (git rm, wc -l).
- Root ZInQKernel.lean: 23 imports removed (deleted files and the Route K/CR3 modules kept only
  for H-reach). AllContrib.lean: 51 imports of deleted files removed.
- Main.lean: CR3 headlines removed; kept `_of_poleCompleteness` (h22); added
  `_of_poleCompleteness_goodPrimeAP`, `_of_poleCompleteness_greenTaoDense`.
  MainGreenTao.lean: `_of_poleCompleteness_goodPrimeDensity` and the headline
  `exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness`.
- OneProof/Main.lean: frozenTarget (r t l) (hPC : PoleCompleteness); imports TailZ74 + MainGreenTao.
- scripts/print_axioms.lean: Route K / CR3 / literature / PropN lines removed, new headlines added.
- Builds: lake build ZInQKernel OK (9923 jobs); +OneProof.Main +Discharges + AllContrib OK;
  every tracked Contrib file OK (15533 jobs); print_axioms: 463 decls, 0 nonstandard;
  frozenTarget axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
- autoform check blueprint: OK. autoform check blueprint --lean-root .: FAILS, 199 dangling `lean:`
  names in 59 blueprint articles (main 10, rank 38, rank-5b 7, route-k 4)
  (scratch/lane74/autoform-check-leanroot-final.txt, per article: blueprint-dangling-articles.txt). blueprint/ is not editable by this task:
  FINDING for #81.
- FINDING: scratch/contrib-check/Check.lean (the chain's CONTRIB-CHECK step) imports deleted modules
  (MainLiterature, GaussFE.Headline, PSide.*, GZDecomp, GZTheta, GZStatements, TYZChain.*).

## #76 (commit 2)

- Parity.lean, Assembly/Local/PoleObstruction.lean, Syntax/Templates/Core.lean restored byte for byte
  from b570b14ee (= git rev-parse 2d8a1fe51^; none changed after 2d8a1fe51). VERIFIED (git checkout).
- Hypotheses/Pole.lean: polePoly T₁ = A(A-e)(A+3e), T₂ = A(Az²-eH)(Az²+3eH); docstrings updated.
  Manuscript lines VERIFIED by grep -n in diophantine_zq.tex: Q_pole align 976-982, Theorem 5.2 (hyp:PC)
  1001-1004, Theorem 5.3 (hyp:RC) 1005-1011 (the brief's "L996-1001" is off by a few lines).
- PoleManuscript.lean: Manuscript.polePoly / PoleSoluble / PoleCompleteness are abbrevs of the ZInQ ones;
  Manuscript.polePoly_eq (rfl) writes out Q_pole. curve/AnalyticRankOne/RestrictedConverse unchanged.
- Builds: lake build ZInQKernel OK (9923 jobs, 7m22s); +OneProof.Main +Discharges + AllContrib OK
  (16104 jobs, 34m46s: the H chain rebuilt because RouteK.Slots.Basic, on the H path, imports Pole.lean);
  every tracked Contrib file OK (15533 jobs); print_axioms 463 decls 0 nonstandard, check_target ok;
  frozenTarget [propext, Classical.choice, Quot.sound]. VERIFIED.
- scratch/lane74/contrib-check-Check.lean (copy of the chain's scratch/contrib-check/Check.lean without the
  20 deleted imports, contribCheck_headline and 112 #print lines of deleted constants): compiles, 117 decls,
  0 nonstandard. VERIFIED.

## #78 (commit 3)

- The headline and frozenTarget edits had to go into commit 1 (OneProof/Main and Main.lean imported deleted
  files, so the tree would not build otherwise). This commit records the signatures:
  scratch/lane74/Signature.lean (output Signature-output.txt), compiled, EXIT 0. VERIFIED:
  ZInQ.OneProof.frozenTarget : OpenResearchLeaves48 → OpenTextbookLeaves18 → OpenAddedLeaves27 →
    ZInQ.PoleCompleteness → ZInQ.FrozenTarget, axioms [propext, Classical.choice, Quot.sound];
  ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness :
    SixContactMin → PoleCompleteness → FrozenTarget, same axioms;
  ZInQ.Manuscript.PoleCompleteness = ZInQ.PoleCompleteness by rfl.
- No h22: the headline goes through route AP with greenTaoDense and Density.goodPrimeDensity.
- On-the-spot: none (no new mathematical statement; the new theorems are old variants with PC for CR₃).

## #79 (commit 4)

- kinds.tsv: rows h21S, hCM, h33c, hBFH, hGZss removed; row hPC added (frozenTarget, kind "manuscript
  hypothesis", GLUE/GLUE, flag "ELLIOT: Theorem 5.3 route in progress (#83)", flag_class note, area_issue
  Deicyde/diophantine-z-q#83). claims/reviews/credits/fold-queue had no TYZ/GZ rows.
- render_open.py: count line and the outside-H section ("Manuscript hypotheses outside the H part").
  autofold.py unchanged: main_state() parses the new Main.lean (binders r t l, sixContactMin_of_open67,
  TailZ74). VERIFIED (python import).
- OpenStatements.lean: 32 open hypotheses (31 H + hPC). render_open.py wrote OPEN.md, pages-wanted.md,
  STATUS.md block; render_open.py --check: ok (note: scratch/contrib-kit/DischargesTest-output.txt was made
  with 36 hypotheses; its owner should rerun it, the check does not fail on it). VERIFIED.
- autoform check blueprint: OK. --lean-root .: 199 errors, all "declaration not found" for removed Route K
  declarations in 59 articles (blueprint-dangling-articles.txt). Unchanged from commit 1; needs #81.
