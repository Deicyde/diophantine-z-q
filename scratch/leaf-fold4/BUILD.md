# leaf-fold4: how Leaves4.lean is built

This directory is leaf-fold3's build (scratch/leaf-fold3/BUILD.md) plus the steps below. parts/ and partsF/c10-c85
are leaf-fold3's outputs (c80 regenerated, step 1).

Order (run from scratch/leaf-fold4):
1. `python3 mk_propts.py`     partsF/c80_propts.lean, re-run on the merged hecke-rest/HeckeRestAll.lean (final version,
                               which proves ChartProper and ChartQuasiFinite). partsF/d90_fold3.lean: the one call of
                               `coverModelOfHecke_of_heckeRest` adjusted by hand (hP, hQ dropped).
2. `python3 mk_periodglue.py` partsF/c90_periodglue.lean (period-map's parts light/theta/siegel/order/heavy, period-glue's
                               BCU, QMTwist, PiTwist, S8, W8, SFA, final_part; uses mk_propts_walk.py = mk_propts.py's walk())
3. partsF/d95_fold4.lean      hand-written (bundles OpenTextbookLeaves4, OpenAddedLeaves4, OpenGlue4 and
                               sixContactMin_of_open4); `python3 mk_d95_glue.py` was run once on the draft to insert
                               gluePieces_of_open4 (from d90's gluePieces_of_open3) and tatePairingZl_of_leaves4 /
                               detTate_of_leaves4; do not re-run it on the current file.
4. `./assemble.sh`            olean/*.lean chain sources (new: LF4T5 = scratch/t5-torsion/T5Full.lean verbatim, TailJ = c90,
                               TailK = d95) and the flat file Leaves4.lean.

Build first (one Lean process): `lake build` of the modules in the `import ZInQKernel…` lines of olean/*.lean
(as leaf-fold3, plus Contrib.ZariskiConn.Basic, Contrib.SpreadOut.NumberField, Contrib.RLeaf.T40 and the imports of
scratch/t5-torsion/T5Full.lean). Contrib.RLeaf.T40 needs t40-clash's fix of the Tau Ceti Backport Units file (merged).

Check: `./chain.sh` compiles LPrefix → TailA-D → LF2Stalks, LF2UnifRoot, LF2SmoothDim, LF2UnramConj, LF3Cot → TailE →
TailF → TailG → TailH → TailI → LF4T5 → TailJ → TailK (`./chain.sh TailJ` restarts from a module), then
`./ctail.sh Check4.lean` (conclusion is the kernel's `ZInQ.SixContactMin`; dependency closure). Or the flat file:
`lake env lean scratch/leaf-fold4/Leaves4.lean` from the repository root (one process, about 18 minutes).
