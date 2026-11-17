# r17-rebase log (results only)

Branch wip/r17-rebase from origin/wip/r17-print 785e3f29; merged origin/main c0f3d085 (leaf-fold33, top
sixContactMin_of_open48 in TailZ55): merge 09ec5c5b, no conflicts (VERIFIED, git).

## Step 1: build on the merged tree
* `lake build ZInQKernel.Contrib.OneProof.CarayolPrinted` (imports NewformDict, CarayolLevel, DSCoeffExt):
  success, 10691 jobs, no edits needed (VERIFIED, 2026-11-16 23:2x).

## New contribution ZInQKernel/Contrib/OneProof/CarayolPrintedIrr.lean (VERIFIED: compiles, no warnings; lake build OK)
* `adjoin_eq_top_of_irreducible_odd`: ρ-family in M₂(K), 2 ≠ 0, no invariant subspace but 0, K², and an involution C in the
  span with det C = −1 ⟹ the K-algebra spanned is M₂(K) (Burnside's form). Proof: e=(1+C)/2, f=(1−C)/2, e a f, f b e lin. indep.
* `CarayolThmAIrr` (leaf): CarayolThmA with the Burnside clause replaced by plain irreducibility (Ribet's word) + oddness
  (∃ c, c*c = 1 ∧ det ρ(c) = −1). `carayolThmA_of_irr : CarayolThmAIrr → CarayolThmA`;
  `carayolR17'_of_printedIrr : CarayolThmAIrr → EigenformCoeffFieldFinite → LadicCond.CarayolR17'`.
* Split: `CarayolExistence` (irreducible, odd, unramified, traces) and `CarayolConductor` (∀ such ρ, condExp = v_p(N));
  `carayolThmAIrr_of_split`, `carayolR17'_of_split`.

## Step 2: clash check (VERIFIED)
* `lake build` of all 244 top-level Contrib modules (contrib-tops.txt, tops.py) + OneProof.Main + Discharges on the merged tree:
  success, 14354 jobs (build-all-summary.txt).
* AllContrib.lean (all 244 tops incl. CarayolPrintedIrr) FAILS on a PRE-EXISTING clash not involving the new modules:
  'PkgI6.TraceContainsRamificationIdx' declared by ZInQKernel.Contrib.Different.Local (only in the closure of the old
  aggregate top ZInQKernel.Contrib.AllContrib) and by ZInQKernel.HDecomp.Textbook.Different (in every OneProof contribution's closure).
* clashloop.sh: dropping ZInQKernel.Contrib.AllContrib, AllContrib2.lean (243 tops incl. CarayolPrintedIrr) elaborates;
  `carayolR17'_of_printedIrr` standard axioms (clashloop-out.txt).
* Dropped top: NewNames.lean lists the 71 constants declared in CarayolPrintedIrr, CarayolPrinted, NewformDict, CarayolLevel
  (new-names.txt); DroppedTopCheck.lean (imports ZInQKernel.Contrib.AllContrib) finds none of them in that environment;
  positive control PkgI6.TraceContainsRamificationIdx found (dropped-top-check.txt). So no name clash from the new modules.

## Step 3: discharges, fold dry runs (VERIFIED, on merged main c0f3d085, top sixContactMin_of_open48 / TailZ55)
* discharges.txt (Discharges.lean): `DISCHARGES [OpenResearchLeaves31.r17]` by
  - `CarayolPrinted.carayolR17'_of_printedIrr`, still assumes [CarayolThmAIrr, DSCoeffExt.EigenformCoeffFieldFinite];
  - `CarayolPrinted.carayolR17'_of_printed`, still assumes [CarayolThmA, EigenformCoeffFieldFinite];
  - `CarayolPrinted.carayolR17'_of_split`, still assumes [CarayolExistence, CarayolConductor, EigenformCoeffFieldFinite];
  all [propext, Classical.choice, Quot.sound]; also adjoin_eq_top_of_irreducible_odd, carayolThmA_of_irr standard.
* autofold dry runs (`autofold.py SPEC --dry-run`, kinds.tsv of main):
  - autofold.json (carayolThmAIrr, published, unread + risks): 11/18 on 29 -> 12/17 on 29; strictest 11/18 -> 12/17.
  - autofold-burnside.json (r17-print's carayolThmA, unread): 11/18 -> 12/17 (same).
  - autofold-split.json (carayolExistence published unread + carayolConductor composite): 11/18 on 29 -> 12/18 on 30.
  - autofold-pending.json (carayolThmAIrr, pending reading): 11/18 -> 11/18 (neutral).
* AutofoldDryRun.lean (line 1 stripped): compiles; `sixContactMin_of_open49` standard axioms (autofold-dryrun-compile.txt).
* FrozenTargetDryRun.lean: Main's imports + dry-run body + `frozenTarget_r17rebase` (Main's frozenTarget with
  OpenResearchLeaves32 and open49): compiles, standard axioms (frozentarget-dryrun-compile.txt).
* AutofoldDryRunSplit.lean: compiles, standard axioms.

## Scenario F (VERIFIED)
* ScenarioF.lean: verbatim copy of ModularSplit.R17.CarayolRealization (diff identical to scratch/modular-split/R17.lean);
  `carayolRealization_of_printed : CarayolThmA → EigenformCoeffFieldFinite → CarayolRealization` and the Irr variant,
  standard axioms (scenarioF.txt). So the printed leaf supersedes modular-split's split as well.

## Step 4/5: rating and counts (report docs/research/r17-rebase.md §4, §6)
* Burnside clause: a step beyond Ribet's printed "irreducible"; PROVED in Lean from irreducible + odd (CarayolPrintedIrr §1).
* Conductor clause: a step beyond Théorème (A) as printed (Carayol (A) + Casselman 1973; locators.md row R17 read: CONSEQUENCE);
  not provable (π_p not definable in Mathlib 4.35); SPLIT off as CarayolConductor (composite) with CarayolExistence; the leaf keeps
  the packaged clause (DDT 1997 Thm 3.1 / Carayol §0.8, UNVERIFIED), flag unread + risk.
* Count on main kinds.tsv: strictest 11/18 on 29 -> 12/17 on 29 (autofold.json); unchanged if pending reading.
