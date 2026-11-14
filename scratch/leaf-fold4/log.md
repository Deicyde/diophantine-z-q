# leaf-fold4 results log

## 17:45 start (fresh; no earlier log)
- Base 8ec80711. Merged origin/wip/leaf-fold3 (f7951690), period-glue (7e1531df), zariski-conn (3802f2bc),
  t5-torsion (58ac8d0b), homlattice (89a1fc02), kerwild-fix (f596943a), frobchain-contrib (f4bf0b72),
  hecke-rest (6c2c1d76; its .fleet note dropped in the merge). spread-out (aa304ed7) was already in the base.
  origin/wip/vert-witness and origin/wip/t40-clash do not exist yet (17:50).
- No leaf-fold3 oleans exist on this host: the whole chain is rebuilt. `lake build` of the kernel modules
  imported by the chain plus Contrib SpreadOut, ZariskiConn, FrobChain started 17:46.
- Copied leaf-fold3's build into scratch/leaf-fold4/ (ctail.sh path changed).
- mk_propts.py re-run on the merged hecke-rest/HeckeRestAll.lean: c80 gains hecke-rest's curve proofs
  (`HeckeRestCurve.chartProper`, `chartQuasiFinite_of_proper`, `curveChartInf`), and
  `HeckeRestAll.coverModelOfHecke_of_heckeRest` no longer takes ChartProper/ChartQuasiFinite.
  d90_fold3.lean: the one call adjusted (hP, hQ unused). assemble.sh: only TailG and TailI differ from leaf-fold3.

## 18:05-18:31 olean chain, VERIFIED compiled
- chain.sh (one Lean process): LPrefix 625 s, TailA 91 s, TailB-TailD, LF2*/LF3Cot 6-13 s, TailE 58 s, TailF 41 s,
  TailG 72 s (c80 with hecke-rest's curve proofs: 0 errors), TailH 77 s, TailI 6 s, LF4T5 (t5-torsion's T5Full.lean
  verbatim) 12 s: all 0 errors.
- TailJ (c90 period-glue) first run: 23 errors. Causes: (1) mk_propts' text-identity dedup dropped period-glue's
  copies of mobius-glue's `AutOExt` lemmas and mul-rigidity lemmas living in other namespaces (TEXT_DEDUP now off
  for c90; nothing is dropped by name either: all period-map/period-glue names are new to the chain); (2) the
  chain's a80_fqm opens `ZInQ.LeafPush2 (CPts cptObj IsUniformization …)` explicitly where FibreQM.lean had
  copies in `HSyn.G0Split`: the same `open` is inserted after each `namespace HSyn.G0Split.FibreQM…` line;
  (3) BCU's `_root_.PeriodGlue.MulRigidity.…` → `_root_.HDec.PeriodGlue.MulRigidity.…` (HDec wrapper).
  Second run: TailJ 31 s, 0 errors.
- TailK (d95) first run: 1 error (`AddCommMonoid (A.T ℓ)` in tatePairingZl_of_leaves4: the original sits under
  `open … MonObj`); fixed with `open … MonObj in`. TailK 13 s, 0 errors; all 17 `#print axioms` lines
  `[propext, Classical.choice, Quot.sound]`, including `HDec.HSyn.sixContactMin_of_open4`.
- Lean accepted by defeq, without any proof work: the kernel's `LeafQM.AV.Pin.autOInnerFinite` for this file's
  `PeriodGlue.AutOInnerFinite`; `TSkolemKW.leafSkolemNoether` for `GlueDescent.LeafSkolemNoether`;
  `ZariskiConn.properSmoothGenConnected_of_zariskiConnectedness` for `FrobPiecesNeron.ProperSmoothGenConnected`;
  `NF.abVarSpreadsOut_of_ega … (toAbVarK4 B)` for `FrobPiecesNeron.AbVarSpreadsOut`; T5/T26 transported between
  the chain's `PkgI2`/`PkgI3` copies and the kernel's (`torsionStructureK_of4`, `tateModuleFree_of_t5'`).
- Counts: 26 + 19 + 20 + 1 = 66 (leaf-fold3: 26 + 20 + 16 + 6 = 68).

## 18:32-18:50 flat file and dependency check, VERIFIED
- olean/Check4.lean (28 s): `example : (∀ r t l g, _root_.ZInQ.SixContactMin) := HDec.HSyn.sixContactMin_of_open4`
  compiles; closure 181 113 constants; contains chartProper, chartQuasiFinite_of_proper, period-glue's proofs, the
  kernel's autOInnerFinite, leafSkolemNoether, properSmoothGenConnected_of_zariskiConnectedness,
  NF.abVarSpreadsOut_of_ega, t5-torsion's tateModuleFree_of_torsionStructure / tate_surj_of_torsionStructure;
  not sorryAx, WeilPairing.DivisiblePoints, the old tatePairingZl_of_leaves / detTate_of_leaves,
  gluePieces_of_open3, LGKerWild.exists_localGlue_of_tateModuleFree.
- Flat run 1 (Leaves4.lean, 118 463 lines, md5 3cbfb09b0186…): exit 0 in 1064 s, 0 errors, no sorry, 325
  `#print axioms` reports, all `[propext, Classical.choice, Quot.sound]` (checked by script over wrapped lines).
- 18:35 merged origin/wip/t40-clash (46595da1; report present; it edits the kernel's Tau Ceti Backport
  Units file only). vert-witness's report (2f557240) read: it reduces HeckeVertWitness to 1 leaf + 3 glue, so it
  is a count variant only (glue 1 -> 3), not folded.

## 18:51-18:58 T40 fold, VERIFIED
- `lake build ZInQKernel.Contrib.RLeaf.T40` after the t40-clash merge: builds. The chain's oleans stayed valid (no
  chain import depends on the Backport Units file).
- d95: field `t40 : X1Belyi.X1RationalCusp` replaced by `x0Transitive : ZInQ.RLeaf.X0Transitive`;
  `t40_of_x0Transitive4 := ZInQ.RLeaf.x1RationalCusp_of_x0Transitive` (accepted for the chain's X1RationalCusp copy).
  TailK 14 s, 0 errors, 18 axiom lines standard. Check4: closure 183 500, contains x1RationalCusp_of_x0Transitive,
  no sorryAx. Same count (66).
- Flat run 2 started 18:58 (Leaves4.lean md5 e7ec3222a537…, 118 476 lines; header now imports Contrib.RLeaf.T40).
- Flat run 2 (md5 e7ec3222a537…): exit 0 in 1054 s, 0 errors, no sorry, 326 axiom reports all standard.
- 19:17 d95 docstrings only (header, OpenAddedLeaves4 docstring: `divisiblePoints` dropped): TailK 13 s, 0 errors,
  18 standard axiom lines. Flat run 3 on the final text started (Leaves4.lean md5 6bbeb639662a…, 118 478 lines).
