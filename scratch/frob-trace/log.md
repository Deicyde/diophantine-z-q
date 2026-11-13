# frob-trace results log

## Setup (2026-11-13 ~06:00)
- Copies (verbatim): part_tate_src.lean = scratch/unram-tate/TateBridge.lean (= g0-mod-field ModField.lean L1-1036 + import RhoCont + section UnramTate);
  part_bridge_src.lean = scratch/g14-trace/part_bridge.lean (G14Bridge.FrobTraceLink, G14Bridge.TateBridge35, tateBridge_five_three_of_35).
- build.sh assembles FrobTrace.lean = `import ZInQKernel.HDecomp.C10.Link` + the two copies + part_frob.lean (this task).
- Built the imported kernel modules with `lake build` (exit 0, ~15 min).
