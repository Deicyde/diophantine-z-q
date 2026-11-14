# leaf-fold6: how sixContactMin_of_open6 is built

leaf-fold4's committed chain sources (scratch/leaf-fold4/olean/{LPrefix,...,TailK}.lean) and leaf-fold5's
(scratch/leaf-fold5/olean/{TailL,TailM,TailN}.lean) are compiled unchanged; this directory adds one module, TailO.

1. Build the kernel modules first (one Lean process): `lake build $(cat scratch/leaf-fold5/kernel_targets.txt)`
   (leaf-fold5's list; TailO needs no new kernel module).
2. Parts (run from scratch/leaf-fold6):
   - `python3 mk_f10.py` parts/f10_leafq.lean (leafq-check's Fold.lean, `import TailK` dropped, its bundle names
     OpenAddedLeaves5..10 / sixContactMin_of_open5..10 renamed with a Q; asserted reversible)
   - parts/f20_fold6.lean: hand-written (bundles, transports, sixContactMin_of_open6, sixContactMin_of_open6_poincare)
3. `./assemble.sh`   olean/TailO.lean (import TailN + f10 + f20) and the flat file Leaves6.lean
                     (= scratch/leaf-fold5/Leaves5.lean + f10 + f20; not committed, md5 in flat.md5)
4. `./chain.sh`      LPrefix ... TailK (leaf-fold4), TailL, TailM, TailN (leaf-fold5), TailO (`./chain.sh TailO`
                     restarts from a module), then `./ctail.sh scratch/leaf-fold6/olean/Check6.lean` (path relative to
                     the repository root): conclusion is the kernel's `ZInQ.SixContactMin`, dependency closure, head
                     constant of every field, field types equal to their source bundles'.
   Or the flat file: `lake env lean scratch/leaf-fold6/Leaves6.lean` from the repository root (one process, ~25 min,
   ~17 GB).
5. `python3 py/verbatim_check6.py > py/verbatim_check6_out.txt` (needs Leaves6.lean and olean/Check6_out.txt).
