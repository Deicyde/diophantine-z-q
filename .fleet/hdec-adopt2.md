# hdec-adopt2 (fleet summary)

**Result.** All eleven glue clusters named by the task are now in the built project: 15 new
modules (about 7,700 lines) under `ZInQKernel/HDecomp/`, imported by `ZInQKernel/HDecomp.lean`.
They are `I3Linalg.{C2,TateBC,RhoCont}` (SemisimpleBaseChange proved; C2′ and E1′ with I3 leaves
only; Tate modules along injective maps; continuity of ρ_ℓ), `Descent.WP3` (LeafHasse and
LeafLocalTwo from T14-T15), `B3Unram.B3b` (B3 (v) from leaf T32(a) only; LeafB3b, LeafConj and
T32(b) proved), `C10.Link` (the C10 trace link), `Vigneras.{Local,Global}`,
`Sqrt.{SqrtLocal,Disj}`, `Conductor.LadicCond` (the conductor exponent, with R17/L8 stated) and
`Assembly.{C8,E1Lin,E2Index,F3Glue}`. No cluster was dropped.

**Verified.** `lake build ZInQKernel` exits 0 (17:03 PST). `lake env lean
scripts/print_axioms.lean` prints 272 axiom lists, 93 of them new, and every one is exactly
`[propext, Classical.choice, Quot.sound]`. There is no `sorry` and no `axiom`, and no line in the
new modules is over 100 characters.

**Copies made into imports.** pkg-I3's object layer in C2, TateBC and RhoCont now comes from
`Objects`, so the old `QMDichotomy` and `I3Leaves` copy is gone; only `QMDichotomyYu` remains. The
other copies replaced by imports:
- WP3: the PkgI6 cochain leaves (from `Conductor.I6Base`) and the glue-descent files.
- Disj: SqrtLocal's lemmas and `LocalKroneckerWeber`.
- B3b: glue-descent's `GQ`, `cyc`, `galChar`, `UnramifiedAt` and lemmas, through
  `open GlueDescent.B2Q (…)`.
- Vigneras.Global: `GlueRepo.A1.{B,comb,combMul}`.

SqrtLocal's `exists_half_iff` and Vigneras' `comb_mul` keep their statements and are now proved
by the project's copies. Superseded drafts, whose content is inside an adopted file, are listed
in `docs/research/hdec-adopt2.md`.

**Remaining.** Two lemmas are proved twice inside `Sqrt/Disj.lean`; both copies come from a draft
that is not an HDecomp module. The build's linter warnings (unused simp arguments, deprecations)
were left as the drafts wrote them. The leaves are still `def … : Prop` hypotheses, by design.
Regenerate with `python3 -I scratch/hdec-adopt2/adopt2.py`.
