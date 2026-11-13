# hdec-adopt5b results log

- 01:16 start (fresh; no earlier log). t10-etale is not in the base: its file is read from
  origin/wip/t10-etale (9610b943) with `git show` into /tmp, never committed as scratch.
- Duplicate scan (scratch/hdec-adopt3/dups.py) of every draft against ZInQKernel/HDecomp:
  t-different All.lean: 10 SAME (pkg-I6 ramification defs + 4 leaf statements, Conductor/I6Base);
  t-skolem-kw: SkolemNoether, LeafSkolemNoether, BrauerNesbittChar0, the whole GlueC10 part of
  FrobeniusDense/C10Closed (C10/C10.lean), HSyn's Qbar/GQ/LiesOver/IsArithFrob (= PkgI4's);
  t30-adelic: none; t10-etale: T10_groupIso (= ZInQ.LeafPush2's); t28-igusa: none.
- Generator scratch/hdec-adopt5b/adopt5b.py writes 15 modules under ZInQKernel/HDecomp/Textbook/;
  wrap.py leaves no line over 100; decls.py finds no new duplicate declaration names.
- 01:4x: Different, SkolemNoether, BrauerNesbitt, C10Closed, FrobeniusDense, KroneckerWeberUse,
  ChebotarevCyclotomic, G1Count, G1Adelic, T30SqrtCrit, T10Etale each build with lake build
  (exit 0). One wrap.py break repaired by hand in Different (fixups.py).
