# leaf-fold5: how sixContactMin_of_open5 is built

leaf-fold4's committed chain sources (scratch/leaf-fold4/olean/{LPrefix,...,TailK}.lean) are compiled unchanged; this
directory adds three modules after TailK.

1. Build the kernel modules first (one Lean process): `lake build $(cat scratch/leaf-fold5/kernel_targets.txt)`
   (the imports of leaf-fold4's chain, of the new parts, and ZInQKernel.Contrib.AVB2.SerreLemma).
2. Parts (run from scratch/leaf-fold5):
   - `python3 mk_e10.py`  parts/e10_vertmodel.lean (vert-witness VertMain.lean.part + model-glue ModelGlue{,2..6}.lean.part, ported)
   - `python3 mk_e20.py`  parts/e20_avb2.lean (av-b2 AVB2Main.lean, namespace AVB2, verbatim)
   - parts/e30_kernel.lean, parts/e40_kernelfields.lean, parts/e90_fold5.lean: hand-written
3. `./assemble.sh`        olean/TailL.lean (e1*), TailM.lean (e2*-e8*), TailN.lean (e9*) and the flat file Leaves5.lean
4. `./chain.sh`           LPrefix ... TailK (leaf-fold4's sources), TailL, TailM, TailN (`./chain.sh TailL` restarts
                          from a module; `./chain.sh TailM TailM` compiles one module), then
   `./ctail.sh scratch/leaf-fold5/olean/Check5.lean` (path relative to the repository root): conclusion is the
   kernel's `ZInQ.SixContactMin`, dependency closure, head constant of every field.
   Or the flat file: `lake env lean scratch/leaf-fold5/Leaves5.lean` from the repository root (one process).
