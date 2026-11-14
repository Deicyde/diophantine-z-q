# leaf-fold6 (fleet summary)

**Result.** `HDec.HSyn.sixContactMin_of_open6 (r : OpenResearchLeaves5) (t : OpenTextbookLeaves6)
(l : OpenAddedLeaves6) (g : OpenGlue6) : ZInQ.SixContactMin` — no `sorry`, axioms
`[propext, Classical.choice, Quot.sound]`, conclusion the kernel's own `ZInQ.SixContactMin`. 68 hypotheses:
26 research + 21 textbook + 20 added + **1 glue** (`ModelCoordinateResidue`). leaf-fold5: 70 (glue 2); leafq-check: 65
over leaf-fold4's bundles.

**What it is.** leaf-fold5's bundles with leafq-check's four reductions: `gammaStarGen` proved;
`valenceBoundGammaStar` → `valenceFormulaGammaStar`; `cmDescends` → `stQM` (with leaf-fold5's T11(b) existence half
and kernel T5, transported); `qmHauptmodul` → `qmHauptmodulBase3`. leafq-check's own `OpenAddedLeaves5..10` /
`sixContactMin_of_open5..10` were renamed `…Q5..Q10` (leaf-fold5's names kept). T8: kept as a leaf on the kernel's
`PkgI3.PoincareReducibility` (glue 1, 68 fields); leaf-fold5's split (PoincareComplement + SimpleImageIsogeny) gives
glue 2, 69 fields, compiled as `sixContactMin_of_open6_poincare`. 32 fields are kernel constants (all of leaf-fold5's
that remain, plus `t8`).

**Kinds (strict rule, report §2.0).** 51 LEAF / 16 LEAF? / 1 GLUE (inherited kinds: 57 / 10 / 1). Moved to LEAF? as
composites: `r1r2`, `r3`, `r11r12`, `r16`, `valenceFormulaGammaStar`, `t8`.

**What compiles (VERIFIED).** Kernel build in this worktree; the full olean chain LPrefix … TailN (leaf-fold4/5
sources unchanged) + TailO, 0 errors, all 369 axiom reports standard; Check6 (kernel conclusion, closure without
sorryAx, field heads, field types `==` their source bundles'); flat file Leaves6.lean (leaf-fold5 flat + the two parts) exit 0 in 1680 s, 0 errors, 369 standard axiom reports;
`py/verbatim_check6.py` ALL OK (field texts, provenance of all 68 head constants, T8 kernel = pkg-I3 = chain,
leafq-check Props).

**What remains.** The glue `ModelCoordinateResidue` (tame quotient `𝒴/Γ' ≅ P¹_{ℤ_(p)}`, not in Mathlib);
16 LEAF? fields; human checks of `ShimuraGoodReduction` (level 3 at 3 | D), `STQM`, `ValenceFormulaGammaStar`,
`R1R2fpRep`, R6's m = 3 boundary. Report: docs/research/leaf-fold6.md; Lean: scratch/leaf-fold6/.
