# sz-raynaud results log

- Base: wip/ga-rigidity f9e83fdb (worktree ~/dzq-wt/sz-raynaud, branch wip/sz-raynaud). No other branch merged.
- diophantine_zq.tex L814-818 (read): F = L_v with A[3] adjoined (A[5] if p = 3), degree <= D G_0 over Q_p;
  "Raynaud's criterion \cite[Theorem 3.5]{silverbergzarhin} gives semistable reduction there"; the next sentence
  (wild inertia of F acts trivially on each V_l(A), l != p) carries no citation. VERIFIED (read).
- Bibliography L11077-11080: Silverberg-Zarhin, AIF 45 (1995) 403-420, Theorem 3.5. `grep -n "SGA\|sga7\|grothendieck"`
  on diophantine_zq.tex: no hit, SGA 7 is not cited anywhere in the manuscript. VERIFIED.
- The manuscript cites Silverberg-Zarhin only at L816 (grep `silverberg`): the only use of Raynaud's criterion. VERIFIED.
- locators.md row R6 (read): SZ Thm 3.5 p. 406 cites SGA 7 IX 4.7, allows torsion over an unramified extension;
  extraction makes the threshold look like `>3`, n = 3 unconfirmed. Second row: SZ Thm 3.3 p. 405 for square-zero
  monodromy (not cited by the manuscript). VERIFIED (read the notes; SZ itself not read, no network).
- kinds.tsv row raynaudSemistableSHOr (read): SGA 7 IX 4.7 p. 366 read 11-17, n > 1 prime to p, only exception n = 2.

## Where the two rows feed (traced in the tree)

- sga7_IX_Cor3_3 -> sga7_IX_3_3_SHpre (TailZ66:88, SGA33Steps.shpre_of_cor33) -> sga7_IX_3_3_SH (TailZ45:90)
  -> semistablePersistsSHcp (TailZ41:88) and sga7_IX_3_3 (TailZ33:104) -> SS3 `ZInQ.HeightSplit.SemistablePersists`
  (NeronDVR.ss1_ss3_of_cpNF, TailZ26:179) -> `r20_of_leaves'` / `r20Lower_of_leaves'` (TailY:618-680): heights of
  A, B computed on Neron models over a common field of semistable reduction (Faltings' Lemma 5 for base changes).
  Not used by D2 (L814-818). VERIFIED (grep + read).
- sga7_IX_3_5_ForwardGeom -> semistableUnipotent (TailZ33:101, UnipotentForward.semistableUnipotent_of_forwardGeom)
  -> r6 `PkgI2.RaynaudCriterionNF` (TailZ26:171, GapNeron.raynaudCriterion_leavesNF with RaynaudSemistable).
  r6 consumers: D2 (TailH raynaudPlace_of_R6 -> torsFix_of_descent -> torsFixWildOdd / tateWildKE / localGlue),
  A6 (TailF qmModelG3_of: QML3 good reduction away from 3), I2 (TailH linkedTateLocal_of_tateBridge35). VERIFIED.
- raynaudSemistableSHOr -> raynaudSemistableSH (TailZ45:87) -> RaynaudSemistable (raynaudSemistable_of_SH_pair,
  with strictHenselizationPair) -> r6 and SS1 (semistableReductionDVR_of_raynaud). VERIFIED.
- In the kernel, D2's "wild inertia acts trivially" is PROVED from r6 (unipotence, i.e. SGA 7 IX 3.5) + the
  p-power period of wild elements (TailH wildIter) + PkgI2.fixed_of_unipSq_of_iterate. VERIFIED (read).
- The manuscript's good reduction away from S comes from the proper model / universal abelian scheme (L529-530),
  not from Raynaud; the kernel's A6 Raynaud route (rv-a6-route) is not the manuscript's route. VERIFIED (read).

## Run 2 (after the host's late note, 11-17 06:24)

- Host's late note copied to scratch/sz-raynaud/sz-thm35-reading.md: SZ Thm 3.5 read from the page image (p. 406):
  any field with a discrete valuation, n not divisible by the residue char, X_n over an unramified extension,
  n >= 3 => semistable; SZ's semistable (p. 405) = identity component of the special fibre (over k) an extension
  of an abelian variety by a torus, not necessarily split. VERIFIED (read, fleet print reader, relayed).
  Known issue R6 (n = 3) is resolved: OCR artefact. No known issue recorded for SZ 3.5.
- SZ's semistability = `DictModels.RaynaudOr.IsSemistableResT` (RaynaudSemistableOr.lean:256:
  `HasSemiAbelianIdCompTorus` of the special fibre over k(s), torus split only over k̄). VERIFIED (read).
  Step SZ form -> kernel form (geometric fibre, split torus) = `isSemistable_of_resT` (RaynaudSemistableOr:271)
  from the bundle leaf GeomConnOfRationalPoint (Stacks 04KV; proved `geomConnOfRationalPoint_proof`).
- Previous run's lake build (started in background by run 1) still running at 06:25 (TailC), left to finish.
- SZR.lean / SZRaynaud.lean revised: `SilverbergZarhinThm35` concludes `∀ Néron 𝒩, IsSemistableResT 𝒩` (SZ's form,
  no disjunction, no UNVERIFIED); `HasSemistableReductionSZ`; `isSemistable_of_sz` (named step SZ -> kernel form);
  ELLIOT leaf over `HasSemistableReductionSZ`, restricted to number fields (the manuscript's setting);
  Def34 variant leaves dropped, replaced by `def34_of_sz35` (SZ -> no G_a, via GaRigidity rigidity).
- autofold.json: discharge raynaudSemistableSHOr by `SZRaynaud.raynaudSemistableSHOr_of_sz35 {n}.silverbergZarhinThm35`.
- Strict dry run (leaf-fold33b autofold.py/render_open.py from d67ea55f6, identical to origin/wip/leaf-fold33b
  74395dcf0): EXIT 0, "strict count: 12/22 on 34 -> 12/22 on 34; strictest 11/23 -> 11/23"; output
  scratch/sz-raynaud/dryrun.txt (OpenResearchLeaves43, sixContactMin_of_open61). VERIFIED (run).
- Run 1's background build killed at TailH (06:29); build2 started: lake build SZRaynaud + OneProof.Main +
  OneProof.Discharges (scratch/sz-raynaud/build2.txt).
- build2: ZInQKernel.Contrib.OneProof.SZRaynaud compiled (6.3s), only warning: haveI -> have style hint at :168 (fixed after). VERIFIED (compiled).
- build2 (07:14): `lake build SZRaynaud OneProof.Main OneProof.Discharges` EXIT 0; frozenTarget axioms
  [propext, Classical.choice, Quot.sound]. Rebuilt SZRaynaud after the style fix: OK, no warnings from it. VERIFIED.
- scratch/sz-raynaud/Discharges.lean (`lake env lean`, EXIT 0, output discharges-out.txt):
  `DISCHARGES [OpenResearchLeaves42.raynaudSemistableSHOr] by SZRaynaud.raynaudSemistableSHOr_of_sz35
   still assumes: [SZRaynaud.SilverbergZarhinThm35]  axioms: [propext, Classical.choice, Quot.sound]`.
  #print axioms of all 11 new theorems: [propext, Classical.choice, Quot.sound] (pow_smul_tate: [propext, Quot.sound]).
  VERIFIED (compiled).
- Dry-run fold output minus line 1 (scratch/sz-raynaud/DryRunFold.lean) compiles, EXIT 0:
  'HDec.HSyn.sixContactMin_of_open61' depends on axioms: [propext, Classical.choice, Quot.sound]. VERIFIED.
