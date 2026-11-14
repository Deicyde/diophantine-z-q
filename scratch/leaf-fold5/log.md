# leaf-fold5 results log

## 2026-11-13 23:30 start
- Base ee7582da (wip/integrate-w52). No earlier run (no log.md).
- Kernel not built in this worktree: `lake build` of the 51 kernel modules the chain and the new parts import
  (kernel_targets.txt) started 23:40.
- Chain plan: leaf-fold4's committed sources scratch/leaf-fold4/olean/{LPrefix,...,TailK}.lean compiled unchanged
  into scratch/leaf-fold5/olean (chain.sh), then TailL (vert-witness + model-glue port, mk_e10.py), TailM (av-b2,
  av-b1, curves-g, neron-c), TailN (bundles, sixContactMin_of_open5).
- mk_e10.py: vert-witness VertMain.lean.part + model-glue ModelGlue{,2..6}.lean.part, hdec edits; no declaration of
  them is already in the chain (0 dropped); `smoothFibreReduced'` now the kernel's `ZInQ.SmoothFibre.smoothFibreReduced`.

## 23:50 kernel built; chain started
- `lake build` of kernel_targets.txt: success (11003 jobs, 23:40-23:49). ZInQKernel.Contrib.AVB2.SerreLemma (av-b2's
  kernel file, imported by part e20) built separately.
- mk_e10.py edits for (c): `smoothFibreReduced'` := the kernel's `ZInQ.SmoothFibre.smoothFibreReduced`;
  `isReduced_of_etale_of_isDomain'` := the kernel's `ZInQ.SmoothFibre.isReduced_of_etale_of_isDomain` (model-glue had
  verbatim copies of both).
- Parts drafted: e20 (av-b2 AVB2Main, verbatim), e30 (t6/t7/t8/t34/t38/t3/t41 from the kernel's AVB1/CurvesG/NeronC
  theorems via toAbVarK4/ofAbVarK4), e90 (OpenTextbookLeaves5 21, OpenAddedLeaves5 21, OpenGlue5 2;
  sixContactMin_of_open5 through leaf-fold4's bundles).
- 23:50 `./chain.sh LPrefix` (LPrefix ... TailK from leaf-fold4's sources, then TailL, TailM, TailN).
