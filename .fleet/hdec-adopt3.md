# hdec-adopt3 (fleet summary)

**Result: all four developments are adopted into the build.** `lake build ZInQKernel` exits 0
(19:46 PST). `lake env lean scripts/print_axioms.lean` prints 332 axiom lists, every one exactly
`[propext, Classical.choice, Quot.sound]`. 60 of them are new (272 before). Report:
`docs/research/hdec-adopt3.md`; log and generator: `scratch/hdec-adopt3/`.

13 new modules under `ZInQKernel/HDecomp/` (about 4,960 lines), all imported from
`ZInQKernel/HDecomp.lean`:
- `B3Unram.T32a` imports `B3Unram.B3b` and leaves out the draft's 1,800-line copy of it. It
  puts `GlueB3Unram.t32a` (leaf T32(a) proved), `leafB3a` and `unramified_outside_noLeaf` (B3 (v)
  resting on no leaf) in the build.
- `ModCurves.{Genus,Defs,Leaves,Glue}`: `IsX1Model`, `IsJacobian`, `IsJ1`, the leaves R16 and
  `JacobianExists`, `DimJ1Genus`, `X1ModelExists` (all `def … : Prop`), and the proved glue
  (`dim_J1_le`, `exists_J1_quotient`, `rhoF_traces`, `g13_constituent`, `rhoF_attached`, …).
- `QM.{Structures,Pairs,Leaves}`: R1fp, R1R2fp, R1rec, R5fp with their objects and glue.
- `Faltings.{HodgeData,IdealLines,Models,Height,Leaves}`: `stableFaltingsHeight`, R19-R21 and the
  conditional acceptance tests.

Statements are unchanged: every kept declaration matches its draft text after whitespace
normalization (scripts in `scratch/hdec-adopt3/`). Verbatim copies became imports:
- 11 `PkgI4` definitions (from `Conductor.LadicCond`) and 4 `GlueAssembly` lemmas (from
  `Assembly.E2Index`) in ModCurves;
- the draft's copy of `PkgI3.AbVar` in Faltings. So R19-R21 are now stated over the shared
  abelian-variety type. As a side effect, the draft's `AbVar.origin` and `AbVar.structMapOn` are
  now named `PkgI3.AbVar.origin` and `PkgI3.AbVar.structMapOn`.

There is no `sorry` and no `axiom`, and no new line is longer than 100 characters.

**What remains:** nothing from this task. The leaves are still hypotheses, and
`scratch/h-decomposition/Leaves.lean` still needs to take in these concrete statements (that
file was outside this task's edit scope).
