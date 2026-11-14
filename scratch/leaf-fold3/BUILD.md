# leaf-fold3: how Leaves3.lean is built

parts/ is leaf-fold2's parts/ (already the output of leaf-fold2's scripts mk_parts.py ... mk_unifdims.py,
see scratch/leaf-fold2/BUILD.md; those scripts are copied here for the record and need not be re-run).

Order (run from scratch/leaf-fold3):
1. `python3 mk_g7bound.py`  g0-assemble3's G7Data bound `[L:ℚ] ≤ D` in parts 75, z85, z86 (run once on leaf-fold2's parts)
2. `python3 mk_lf3.py`      partsF/c10, c20, c40, c50, c60, c70, c75 and LF3Cot.lean.src (c30, d90 are hand-written)
3. `python3 mk_propts.py`   partsF/c80_propts.lean (Prop. TS: prop-ts, prop-ts-glue, ts-kummer, kummer-comp, hecke-rest)
4. `python3 mk_ltlocal.py`  partsF/c85_ltlocal.lean (lt-local, unram-roots, frob-pieces; deduplicated against the chain)
5. `./assemble.sh`          olean/*.lean chain sources and the flat file Leaves3.lean (runs mk_prefix.py: issue #2 items)

Check: `./chain.sh` compiles the olean chain LPrefix → TailA-D → LF2Stalks, LF2UnifRoot, LF2SmoothDim,
LF2UnramConj, LF3Cot → TailE → TailF → TailG → TailH → TailI (one Lean process at a time; `./chain.sh TailF`
restarts from a module). Or the flat file: `lake env lean scratch/leaf-fold3/Leaves3.lean` (one process).
Build first: `lake build` of the modules in the `import` lines of olean/LPrefix.lean, olean/TailE.lean and
olean/TailF.lean (kernel Contrib T14, T28, RLeaf, Mobius, Dim, HodgeBC2, TwistDescent, FrobPieces, TauCeti LocalField).
