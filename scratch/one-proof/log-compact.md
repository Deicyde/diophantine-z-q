# op-compact log

## Step 1: baseline (commit 053cbad0)
- `lake build +ZInQKernel.OneProof.Main`: OK (full rebuild of the OneProof modules, ~12 min wall).
- `lake env lean scratch/one-proof/DumpCompact.lean` > dump_before.out: frozenTarget type -> frozenTarget_type_before.txt;
  axioms `[propext, Classical.choice, Quot.sound]`; hashes of type and value of all 8202 constants of the
  `ZInQKernel.OneProof` modules -> hashes_before.txt.
- Sizes before: 80137 lines, 8224119 bytes in ZInQKernel/OneProof/H (1089 tagged alias opens removable).

## Step 2: export aliases instead of repeated alias opens
- scratch/one-proof/compact.py: removes the 1089 tagged `open _root_.Q (...) -- op-dedupe` lines (keeps the 71 that
  replace an original explicit-list open, below `-- op-dedupe was:`), and adds once per module, after the imports,
  `namespace HDec.T export _root_.T (...) end HDec.T` for the names first aliased there: `HDec.Q.r` becomes an alias
  of the kernel's `Q.r`, the name of the deleted copy, so references resolve as they did to the copy.
- LPrefix lines 2659/2955 `open Real ZInQ` -> `open Real _root_.ZInQ` (they opened the root ZInQ because HDec.ZInQ was
  not yet a namespace there; the alias block registers it at the top).
- build1: FAILED in LPrefix, 6 errors `Unknown constant PkgI2.IsAbelianVariety.proper`, `AbVar.grp`, `NF.fld`,
  `GroupModel.grp`, `FinExt.field`: an alias `x` does not give `x.y` (an explicit open does, by prefix).
  Fix: scratch/one-proof/Children.lean lists the 648 non-internal constants below the 2873 targets
  (export_children.txt); compact.py aliases them too.
- build2: FAILED in LPrefix: children defined in kernel modules not yet imported there (`PkgI3.AbVar.dim_baseChange`,
  `.congr_simp` realized in later modules) made whole export lines fail. Fix: Children.lean records each child's
  module; compact.py aliases a child in the first module whose import closure reaches it.
- build3: LPrefix, TailA, TailB OK; TailC:5959 `Ambiguous term LeafQM.AV.QML3.goodReduction`: the chain still
  declares `HDec.LeafQM.AV.QML3.goodReduction` (kept copy) and the child alias landed on the same name. Fix: no alias
  for a child `c` with `HDec.c` declared (3 such: that one, `PkgI3.AbVar.instIsCommMonObjOverSchemeSpecOfX`,
  `ZInQ.DefFaltings.HodgeData.ofIdeal`).
- build4: whole chain OK, frozenTarget axioms standard, frozenTarget type unchanged; BUT hash check: 8 TailE
  constants changed (`HDec.ZInQ.Contrib.AbVarBC.abVarBaseChangeK_of_mulIsogeny`, `torsionDescends_of_mulIsogeny`, ...):
  inside `namespace HDec.ZInQ.Contrib.AbVarBC`, `G0FibreSimple.MulIsogeny`/`MulRigidity.X` resolved to the declared
  `HDec.G0FibreSimple.MulIsogeny`/`HDec.MulRigidity.X` (outer namespace level), and the alias at the inner level now
  wins. Fix: an alias `HDec.q1..qk.r` that would shadow a declared `HDec.q1..qi.q(j+1)..qk.r` (i<j) is not
  exported (36 names: `ZInQ.Contrib.AbVarBC.G0FibreSimple.MulIsogeny`, 35 `ZInQ.Contrib.AbVarBC.MulRigidity.*`);
  their alias opens are kept, merged per namespace into one line each after `namespace HDec` (TailE 5 lines,
  TailF/TailH/TailJ 1 line).
- build5: whole chain OK (`lake build +ZInQKernel.OneProof.Main`, Main reports `[propext, Classical.choice,
  Quot.sound]`). DumpCompact after: frozenTarget_type_after.txt identical to before (diff empty), axioms the three
  standard ones; cmp_hashes.py: 8202 constants before and after, 0 changed (type and value hashes).

## Step 3: report
- Sizes: 8224119 -> 4195116 bytes, 80137 -> 79208 lines (table in docs/research/op-compact.md,
  scratch/one-proof/compact_table.md). build*.out trimmed to error/summary lines.
