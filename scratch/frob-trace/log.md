# frob-trace results log

## Setup (2026-11-13 ~06:00)
- Copies (verbatim): part_tate_src.lean = scratch/unram-tate/TateBridge.lean (= g0-mod-field ModField.lean L1-1036 + import RhoCont + section UnramTate);
  part_bridge_src.lean = scratch/g14-trace/part_bridge.lean (G14Bridge.FrobTraceLink, G14Bridge.TateBridge35, tateBridge_five_three_of_35).
- build.sh assembles FrobTrace.lean = `import ZInQKernel.HDecomp.C10.Link` + the two copies + part_frob.lean (this task).
- Built the imported kernel modules with `lake build` (exit 0, ~15 min).

## Run 1 (06:10): first compile of the draft
- `lake env lean scratch/frob-trace/FrobTrace.lean`: 2 errors (Algebra.IsAlgebraic.tower_top argument; a theorem without type). Fixed: `extendScalars (R := ℚ)`; removed the untyped composite.
## Run 2 (06:15): VERIFIED
- exit 0, 0 errors, no `sorry`, ~60 s. All `#print axioms` standard [propext, Classical.choice, Quot.sound], incl.
  FrobTrace.tateMapEquiv, conj_baseChange, frobCompare_opV_conjE, g7Out_rescale, scalarsQbar,
  tateBridge35_of_algFrobLink : PkgI3.TateModuleFree → AlgFrobLink → G14Bridge.TateBridge35.
- Remaining glue: `FrobTrace.AlgFrobLink` (points-level reduction mod p of the algebraic maps m_σ). Leaf: I3.M0 TateModuleFree.
