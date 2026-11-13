# leaf-fold2 results log

Marks: VERIFIED (compiled / read in a file), STANDARD, SPECULATIVE, UNVERIFIED.

## Setup (2026-11-13 08:45-09:20 PST)
- Base: scratch/h-decomposition/Leaves.lean (35 850 lines, `namespace HDec`, leaf-fold) and
  scratch/g0-assemble2/parts (41 parts; written against the pre-leaf-fold Leaves.lean, VERIFIED by diff:
  g0-assemble2/Leaves.lean = h-decomposition/Leaves.lean before leaf-fold's edits).
- Layout (assemble.sh): olean/LPrefix (mk_prefix.py) -> TailA (parts/[0-9]*) -> TailB (a10-a44) ->
  TailC (a45-a95) -> TailD (z*) -> TailE (b10 AbVarBC copy, b20 fold; imports T14.Main, T28.Assemble,
  RLeaf.X1ConstantField and LF2ImagePlane = scratch/image-plane/ImagePlaneFinal.lean verbatim).
  Flat file Leaves2.lean = all of it.
- Edits to g0-assemble2's parts (mk_parts.py): `_root_.PkgI4` -> `_root_.HDec.PkgI4` (16); `open ZInQ ...`
  -> `open _root_.ZInQ ZInQ ...` (10), as leaf-fold did for Leaves.lean.
- Prefix edit (mk_prefix.py): the ten `TextbookLeaves` fields that g0-assemble2 §7 found unused
  (t1, t2, t3, t4, t16b, t20, t21, t28, t29a, t29b) are deleted from the structure and from
  `textbookLeaves_of_open`; the compile then checks that nothing uses them.
- Statement checks by structure: kernel Props over Mathlib-only definitions transfer by `exact`
  (leaf-fold's method). Props over file-defined structures (AbVar, ToP1) do not: AbVarBC is copied
  (part b10, mk_abvarbc.py); image-plane's C2K/C3K use `ToP1`, converted field by field (`toP1K`).
