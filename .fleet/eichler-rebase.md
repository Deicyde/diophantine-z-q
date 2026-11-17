# eichler-rebase (fleet note)

**Result: `gonzalezRotgerProp56X6` is removed on current main (c0f3d085, top `sixContactMin_of_open48`), −1 GLUE,
no new leaf.** eichler-bound's `EichlerBound.r5fpCountLe_proof` is rebased as a fold candidate. Report:
docs/research/eichler-rebase.md; log: scratch/eichler-rebase/log.md.

What compiles (VERIFIED):
* Merge of origin/main into wip/eichler-bound: no conflicts. `lake build ZInQKernel.Contrib.OneProof.R5fpCountLe`
  (EichlerBound/*, GR56Lattice): OK with **no edits**. Main, Discharges and GRDict also build.
* Clashes: 0 between the 14 new modules and any module of main's Contrib closure (ClashScan.lean reads the oleans of
  16716 modules). The one-file import of all Contrib does not elaborate even on main alone: there are 103
  pre-existing clashes, e.g. `PkgI6.TraceContainsRamificationIdx` in HDecomp.Textbook.Different and
  Contrib.Different.Local, and `ZInQ.GZWeil.*`. These are for maintainers.
* Bypass regenerated against open48 (taint-driven copy, `gen/gen.py` + `Taint.lean`; 104 declarations copied
  `_eb`; the live consumer is now homfree's `fibreComTrivialFull_of_leaves_hf''`, so one line of new glue
  `_hf''_le`): `scratch/eichler-rebase/BypassFold.lean` compiles. `sixContactMin_of_open49` and
  `ZInQ.Contrib.TYZChain.frozenTarget_E` (Main's frozenTarget over `OpenResearchLeaves32` = 31 minus prop56, no
  added field) use [propext, Classical.choice, Quot.sound].
* `#discharges`: 35 open, 10261 checked; no direct discharge, since R5fpCountLe is weaker and the bypass does the
  removal. Count dry-run on main's kinds.tsv: **strictest 11/18 on 29 -> 11/17 on 28**.

What remains: the integrator's fold. Recipe in report §7: install `fold/EichlerBoundCopy.lean.txt` and
`fold/TailZ56.lean.txt` (or regenerate on the then-current top), patch Main as frozenTarget_E does, and drop the
kinds/claims rows. PRs #54 and #55 were not merged.
