# leaf-fold2: how Leaves2.lean is built

Order (each script edits files under parts/ or writes *.lean.src):
1. `python3 mk_parts.py`      copy g0-assemble2's parts (HDec name edits)
2. `python3 mk_a75.py`        part a75 with kernel-field's current New.lean
3. `python3 mk_fix_tailA.py`  part 70 de-duplication, part 77 proof repair
4. `python3 mk_fix_b.py`      part a30 de-duplication, `ConjUniformization` update
5. `python3 mk_fix_c.py`      part a75/a95 fixes
6. `./mk_b05.sh`, `./mk_b07.sh`, `./mk_b08.sh`, `python3 mk_abvarbc.py`, `python3 mk_unifdims.py`
7. `./assemble.sh`            olean/*.lean chain sources and the flat file Leaves2.lean
   (mk_prefix.py is run by assemble.sh; part b20_fold.lean and LF2UnramConj.lean.src are hand-written/copied)

Check: `lake env lean scratch/leaf-fold2/Leaves2.lean` (one process, ~17 min), or the olean chain with
`./ctail.sh <Module>.lean <Module>` in the order LPrefix, TailA-D, LF2ImagePlane, LF2Stalks, LF2UnifRoot,
LF2SmoothDim, LF2UnramConj, TailE (LPrefix: `lake env lean -o olean/LPrefix.olean olean/LPrefix.lean`).
