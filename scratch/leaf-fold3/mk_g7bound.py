#!/usr/bin/env python3
"""leaf-fold3: g0-assemble3's G7Data fix (its parts 75, z85, z86; docs/research/g0-assemble3.md §0, §4):
G7Data records G4's bound `[L:ℚ] ≤ D` as its last clause; `g7OutUnr_of_g4Out` passes G4Out's `hLD`;
`g7Out_of_g7OutUnr` drops it; three projections `….2^11` become `….2^11.1`. The edits are g0-assemble3's
text exactly (diff against scratch/g0-assemble3/parts/*.lean is the HDec header/open lines only)."""
import sys
def edit(fn, pairs):
    s = open(fn).read()
    for a, b in pairs:
        assert s.count(a) == 1, (fn, a[:60], s.count(a))
        s = s.replace(a, b)
    open(fn, 'w').write(s)
edit('parts/75_modfield.lean', [
 ("`L'` unramified outside `T` (Galois form), and `A_{L'}` a model of `P`'s surface. -/",
  "`L'` unramified outside `T` (Galois form), and `A_{L'}` a model of `P`'s surface; and G4's bound\n`[L:ℚ] ≤ D` (added by g0-assemble3, as g8-object and linked-tate recommend). -/"),
 ("(T u) ∧\n  IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P\n",
  "(T u) ∧\n  IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P ∧\n  Module.finrank ℚ L ≤ heightD\n"),
 ("hunr L' hGL', isModelOver_baseChange hle A P hA.isModelOver⟩",
  "hunr L' hGL', isModelOver_baseChange hle A P hA.isModelOver, hLD⟩"),
 ("    hβe, hGL', hdeg, -, hM⟩ := h", "    hβe, hGL', hdeg, -, hM, -⟩ := h"),
 ("    hdata.2.2.2.2.2.2.2.2.2.2.2, hM, hJ,", "    hdata.2.2.2.2.2.2.2.2.2.2.2.1, hM, hJ,"),
])
edit('parts/z85_modelg3g6.lean', [("hπ, hD.2.2.2.2.2.2.2.2.2.2.2⟩", "hπ, hD.2.2.2.2.2.2.2.2.2.2.2.1⟩")])
edit('parts/z86_noncomm.lean', [("P.A hD.2.2.2.2.2.2.2.2.2.2.2 P.surface", "P.A hD.2.2.2.2.2.2.2.2.2.2.2.1 P.surface")])
print('ok')
