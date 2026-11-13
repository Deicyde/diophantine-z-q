# alg-frob-red results log

## Setup (2026-11-13 06:40)
- src_part_tate_src.lean, src_part_bridge_src.lean, src_part_frob.lean: verbatim copies of
  origin/wip/frob-trace:scratch/frob-trace/{part_tate_src,part_bridge_src,part_frob}.lean (commit 87ed8c54).
- build.sh assembles AlgFrobRed.lean = `import ZInQKernel.HDecomp.C10.Link` + the three copies + part_red.lean.
  VERIFIED: the first 2780 lines of AlgFrobRed.lean are `cmp`-identical to frob-trace's FrobTrace.lean.
- `lake build` of the imported kernel modules: exit 0.

## Run 1-2: conjugation and finite-set split
- Statements: AlgFrobRedAt (AlgFrobRed with σ Frobenius at v itself), GoodRedCofinite (leaf candidate: good reduction
  at v ∩ L for v | p, p ∉ S), AlgFrobRedGood (local glue at one place of good reduction).
- Proved: smul_mem_nonunits, liesOver_smul, isArithFrob_conj, algFrobRed_of_at : AlgFrobRedAt → AlgFrobRed,
  algFrobRedAt_of_good : GoodRedCofinite → AlgFrobRedGood → AlgFrobRedAt, algFrobRed_of_good, tateBridge35_of_good.
- Run 2: `lake env lean scratch/alg-frob-red/AlgFrobRed.lean` exit 0, no error, ~46 s; all axiom prints
  [propext, Classical.choice, Quot.sound] (VERIFIED).
