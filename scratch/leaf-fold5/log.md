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
