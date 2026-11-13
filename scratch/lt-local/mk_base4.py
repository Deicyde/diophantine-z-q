# Base4.lean = Base.lean with g0-assemble3's G7Data fix (scratch/g0-assemble3/parts/75_modfield.lean:
# clause `Module.finrank ℚ L ≤ heightD` appended to `G0ModField.G7Data`) and its three proof
# adjustments in g0-mod-field ported verbatim; further adjustments in later copies listed below.
import sys
s = open('Base.lean').read()
reps = [
("""  GlueB3Unram.GalUnramifiedOutside L' (T u) ∧
  IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P

/-- **G7's output with the twist**""",
"""  GlueB3Unram.GalUnramifiedOutside L' (T u) ∧
  IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P ∧
  Module.finrank ℚ L ≤ heightD

/-- **G7's output with the twist**"""),
("""    twist hβe₁ _, hGL', ?_, hunr L' hGL', isModelOver_baseChange hle A P hA.isModelOver⟩""",
 """    twist hβe₁ _, hGL', ?_, hunr L' hGL', isModelOver_baseChange hle A P hA.isModelOver, hLD⟩"""),
("""    hβe, hGL', hdeg, -, hM⟩ := h""", """    hβe, hGL', hdeg, -, hM, -⟩ := h"""),
("""    hdata.2.2.2.2.2.2.2.2.2.2.2, hM, hJ, hMle, hdata.2.2.2.2.2.2.2.2.2.1, hCC⟩""",
 """    hdata.2.2.2.2.2.2.2.2.2.2.2.1, hM, hJ, hMle, hdata.2.2.2.2.2.2.2.2.2.1, hCC⟩"""),
]
for a, b in reps:
    n = s.count(a)
    if n != 1:
        sys.exit(f"count {n} for: {a[:60]}")
    s = s.replace(a, b)
open('Base4.lean', 'w').write(s)
