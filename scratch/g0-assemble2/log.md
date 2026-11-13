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
- TailB (a10-a40) to olean: VERIFIED exit 0, 0 errors (152 s).
- TailC runs: (1) ambiguity `TSkolemKW.KW.Qbar`/`PkgI4.Qbar` in a50 (fix: `open TSkolemKW.KW hiding Qbar GQ`);
  dangling docstring in a55; fibre-cover's `obtain ⟨-, -, -, hnat⟩` on the old 4-clause R1fpProps (now 6
  clauses: `⟨-, -, -, hnat, -, -⟩`); kernel-field: `UnramifiedAt` ambiguous between
  `GlueDescent.B2Q` and Leaves.lean's copy `GlueB3Unram.UnramifiedAt` (fix: `open GlueB3Unram hiding
  UnramifiedAt` where both are opened), duplicate FS5 copy removed; a80 needs leaf-push2's `CPts`,
  `IsUniformization`, `cDom`, `cEvalAt` opened (as part 80). (2) 11 errors: a80 `cDom`/`cEvalAt`; a85:
  `Module.Free` instance timeout in kernel C10/Link.lean's `trace_endE_indep` (fix:
  `set_option synthInstance.maxHeartbeats 400000 in`), `dsimp` no progress. (3) 3 errors: missing
  `letI : NumberField L'` in `linkedTateData_of_local`.
- TailC run 4 (07:2x, 135 s): VERIFIED exit 0, 0 errors, no sorry; `HSyn.gluePieces_of_gluePieces3`,
  `HSyn.sixContactMin_of_leaves3`: [propext, Classical.choice, Quot.sound]. So the whole chain
  LPrefix -> TailA -> TailB -> TailC compiles with every wave-27 part and GluePieces3 (39 fields).
- Finding (VERIFIED, read in Leaves.lean L21906, L21934, L33345ff): `HSyn.ResearchLeaves` has two fields whose
  types are `opaque` placeholders (`r1an : R01b_ComplexUniformization`, `r17 : R17_Carayol`), so it cannot be
  inhabited; neither field is used by any proof (grep). Part z80: `ResearchLeaves3` = the same structure
  without them and with `h5` replaced by `h5fin : StableHeightFinite` (`ResearchLeaves3.h5` rebuilds H5 with
  h5-glue's `neronModelMinimal`); the seven consumers (reverseIsogeny_of_leaves, g8_g12_of_leaves,
  newformLeaves_of, afterG7_of, hom_of_common, glueOutputs_of_leaves, sixContactMin_of_leaves) copied verbatim
  with `r : ResearchLeaves3`; `researchLeaves3_of : ResearchLeaves → ResearchLeaves3`.
- TailC to olean (142 s) and TailD (z80, z90; 7 s): VERIFIED 0 errors, no sorry; `gluePieces_of_gluePieces3`,
  `sixContactMin_of_leaves3 (r : ResearchLeaves3) (t : TextbookLeaves) (gp : GluePieces3)`,
  `sixContactMin_of_leaves3'`, `researchLeaves3_of`: [propext, Classical.choice, Quot.sound].
- Flat file `lake env lean scratch/g0-assemble2/G0Assemble2.lean` (66352 lines, without a95): VERIFIED exit 0 in 749 s, 0 errors, no sorry, 200 `#print axioms` reports all [propext, Classical.choice, Quot.sound] (two printed over three lines) (07:21-07:34).
- Part a95 (g9-derham, ZInQKernel/Contrib/G9 17 proof files, minus its layer copies I3Layer/I4Layer/Statement):
  run 1: bare names inside its reopened `namespace PkgI4.DR` (now `ZInQ.Contrib.G9.PkgI4.DR`) do not see
  Leaves.lean's root `PkgI4.DR` (fix: `open _root_.PkgI4.DR`); run 2: `open PkgI4` resolves only to the
  innermost match `ZInQ.Contrib.G9.PkgI4` once that exists (fix: `open _root_.PkgI4 ZInQ.Contrib.G9.PkgI4`);
  run 3 (TailE = TailC + a95): VERIFIED 0 errors, 58 s.
- GluePieces3: field `g9Glue` replaced by `g9AbVarBaseChange` (GLUE) and `g9R10Weights` (LEAF, Hodge–Tate
  vanishing; g9-derham recommends it as a clause of R10), via `ZInQ.Contrib.G9.g9Glue_of_abVarBaseChange`
  (40 fields: 15 LEAF, 3 LEAF?, 22 GLUE). TailC (with a95) to olean 158 s, TailD 6 s: VERIFIED 0 errors,
  four main theorems standard axioms.
- Part z85: `ModelG3G6` from `G0Split.FibreSimple` (EndDivision of G7's model `A_{L'}`, a `FibreOver` via G7Data's
  `IsModelOver`), `ModelNoncomm` and `ModelG3` (`modelG3G6_of`). GluePieces3: `modelG3G6` replaced by
  `modelNoncomm`, `modelG3` (41 fields: 15 LEAF, 3 LEAF?, 23 GLUE); `fibreSimple_of_gp3` factored out.
  TailD: VERIFIED first run, 0 errors, four main theorems standard axioms.
- Flat file with a95 (g9) and z85 (70428 lines): VERIFIED exit 0 in 739 s, 0 errors, no sorry, 200 axiom reports all standard (07:43-07:56).
- Part z86: `ModelNoncomm` proved (`modelNoncomm_of_mulIsogeny`): with `ψ = endBC ∘ endBC ∘ ι`, commuting
  `ψ(i), ψ(j)` give `12 = 0` in `End(A_{L'})` (`ij = -ji`, `i² = 2`, `j² = -3`, `noncomm_ring`); `[12]` is an
  isogeny (MulIsogeny), so the zero endomorphism `toUnit ≫ η` would be surjective, making `A_{L'}` a
  subsingleton space of Krull dimension ≤ 0 (`topologicalKrullDim_zero_of_discreteTopology`), against
  `dim = 2` (`model_dim`). Runs: placeholder `End _` not inferable; `noncomm_ring` left `-4 • 3 = -1 • 12`
  (use `norm_num`); explicit `A` for `hMul`. Run 4: VERIFIED 0 errors. GluePieces3: field `modelNoncomm`
  removed (40 fields: 15 LEAF, 3 LEAF?, 22 GLUE); four main theorems standard axioms.
