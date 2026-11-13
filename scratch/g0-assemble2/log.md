# g0-assemble2 results log

## 2026-11-13
- Merged origin/wip/{conj-twist,mul-rigidity,fs5-nocm,fibre-qm-period,kernel-field} (all have reports).
- scratch/g0-assemble2/Leaves.lean = copy of current scratch/h-decomposition/Leaves.lean (with pin-apply:
  R1famProps, R1univProps, MobiusGlue, GluePiecesPin). It differs from g0-assemble's copy (pre-pin-apply).
- parts/ copied from scratch/g0-assemble/parts (g0-assemble's 18 part files); scripts adapted to this dir.
- GluePieces.productModelHeight : ZInQ.H5Neron.ProductModelHeight (VERIFIED, Leaves.lean L34252ff), the
  target of product-height.
- TailA (LPrefix + g0-assemble's 18 parts, with part 40's `r1fpProps_twistBy` and `fibreComTrivial_twisted` removed: after pin-apply the repaired `R1fpProps` is not invariant under `Φ ↦ Φ∘σ`; run 1 error 'introN failed' at that proof): run 2 VERIFIED exit 0, 0 errors, no sorry, 113 s (06:42).
- New parts a10-a80 (one per wave-27 task; headers give source lines and every change). TailB run 1: `open
  MorphismProperty` of fs1-descend leaked (ambiguous `Over.w`); fixed by wrapping each new part in its own
  section. conj-twist cut left a dangling docstring (fixed: lines 84-191, 206-1612) and needs its
  `noncomputable section`. Run 2 (06:50, 181 s): parts a10-a40 (fs1, mul-rigidity, height-bc,
  product-height, g10+conj-twist, g12-det, swan) VERIFIED 0 errors; errors only in a45 (unram-tate:
  missing ModField file-level `open`s), then Lean stopped after 100 errors.
- Split TailB (a10-a44) / TailC (a45-z99) for faster iteration.
