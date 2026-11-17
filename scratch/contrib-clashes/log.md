# contrib-clashes results log

- Base: main e1b31749 (origin/main identical; merge = already up to date).
- Contrib modules: 4369 (`git ls-files 'ZInQKernel/Contrib/*.lean'`, list in contrib-modules.txt); 678 had no olean
  in the copied build tree at start; building all 4368 (minus AllContrib) with lake.
- VERIFIED: `lake build` of all 4368 Contrib modules (minus AllContrib) on e1b31749: success, 14380 jobs, 0 errors.
- VERIFIED: baseline (Baseline.lean) recorded in baseline-before.txt (219 lines): frozenTarget type and axioms
  [propext, Classical.choice, Quot.sound]; sixContactMin_of_open55 type/axioms; `#discharges` output.
- VERIFIED (scan-before.txt, ClashScan.lean, olean scan of the closure of all 4368 modules, 16744 modules,
  810239 constants): 79 duplicate non-auxiliary names among them 74 involving project modules:
  66 HDecomp.Textbook.Different / Contrib.Different.Local, 3 ZInQ.GZWeil.{jacobiLambdaDeriv,
  etaModelDifferential, modularParamC1} (WeilJacobi / JacobiLambdaDeriv), 3 CloudW07 auto-named local instance
  `...instPreservesZeroMorphisms..._zInQKernel` (Modules/Extension vs Cohomology/{Flasque, DirectImage/Affine,
  AcyclicResolution}), 1 `ZInQ.Contrib.HP23Proof.instFactPrimeValNat_zInQKernel_1` (Case1/Case3),
  1 `ZInQ.Contrib.TYZGenusFold.instFactPrimeValNat_zInQKernel` (Ideles/Local); 5 in Lean core/Mathlib (ignored).
- VERIFIED (Lean 4.35 source, Lean/Environment.lean `finalizeImport`, `subsumesInfo`): a duplicate constant is
  accepted on import iff both are theorems with equal type, level params and `all` (or theorem/axiom, or
  Prop-typed axiom/axiom); anything else throws "environment already contains". So of the 74, only the 6
  definitions of Different (TDifferent.phiF, phiExpl, filtR, resHom, PkgI6.MonogenicDVR,
  PkgI6.TraceContainsRamificationIdx) are fatal; the other 68 are identical theorems (accepted; e.g.
  TYZLcalOne imports both WeilJacobi and JacobiLambdaDeriv and builds).
- VERIFIED: AllImport.lean (imports all 4368 modules) before the fix: `error: import
  ZInQKernel.HDecomp.Textbook.Different failed, environment already contains
  'PkgI6.TraceContainsRamificationIdx' from ZInQKernel.Contrib.Different.Local` (7.4 GB, 17 s).
- Fixes (commit "remove the Contrib declaration clashes"):
  1. Contrib/Different/Local.lean: body (identical to HDecomp/Textbook/Different.lean up to line breaks,
     checked with diff) replaced by `import ZInQKernel.HDecomp.Textbook.Different` (canonical); 66 names.
  2. GrossZagierHeegner/WeilJacobi.lean imports JacobiLambdaDeriv (canonical); its own proof renamed
     `jacobiLambdaDeriv_viaCuspForms` (same type, used by its `shimuraCMParamCd_proved`); its copies of
     `etaModelDifferential`, `modularParamC1` removed (identical statements, now imported).
  3. HP23Proof/Case3.lean, TYZGenusFold/Local.lean: `local instance (p : Nat.Primes) : Fact p.1.Prime` made
     `private local instance`.
  4. CloudW07 Cohomology/{Flasque, DirectImage/Affine, AcyclicResolution}.lean: the anonymous local
     PreservesZeroMorphisms instance made `private`; third comment line and NOTICE updated (vendored files).
