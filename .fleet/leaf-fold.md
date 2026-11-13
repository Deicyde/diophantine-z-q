# leaf-fold (2026-11-13)

**Result.** `scratch/h-decomposition/Leaves.lean` now states exactly which leaves remain:
`HDec.HSyn.sixContactMin_of_open (r : OpenResearchLeaves) (t : OpenTextbookLeaves)
(gp : GluePieces) : ZInQ.SixContactMin`. The file compiles: 0 errors, no `sorry`, all 210
`#print axioms` outputs `[propext, Classical.choice, Quot.sound]`, 8 min 57 s
(`scratch/leaf-fold/compile4.txt`).

**Open: 50 leaves** = all 23 research-level leaves (26 fields; R10 and R14 in corrected form,
R1(b) and R17 still opaque) + 27 of 35 textbook leaves (26 fields: T1, T3-T11, T14, T16(b), T23,
T24, T26-T29, T33-T35, T36-T40, T41), plus the ten glue pieces (unchanged).
**Folded in as theorems:** T2 (t-brauer-purity's proof copied in), T15, T16(a), T17, T18,
T20, T21 (global), T25, T31, each from its `ZInQKernel/Contrib/` proof. T30 now has a closed proof
as well; T13, T19 and T22 were already out of the bundle.

**How.** The kernel port `ZInQKernel/HDecomp/` declares the file's names at the root, so the whole
file is wrapped in `namespace HDec` (all names gain the prefix `HDec.`). The file was then patched
for the side effects of the new imports: Tau Ceti's `FinitePadicExtension` instances are switched
off inside `HDec` (instance-search timeouts), Mathlib's `AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt`
is called explicitly (a Tau Ceti lemma had captured the dot notation), and T19 is the identical
kernel proof. The whole file is rebuilt with `python3 scratch/leaf-fold/assemble.py`.

**Statement checks.** Every Contrib conversion is accepted by `exact` (definitional equality).
The new command `#hdec_same` compares the statements syntactically, up to the `HDec.` prefix and
the names of proofs. 14 of 15 checks are verbatim. The exception is T25: the elaborated body of
`PkgI4.HasNebentypus` differs, although the source text is the same; the two are still
definitionally equal (the `exact` conversion succeeds).

**Repairs.** R14 is now `G0Galois.R14Det` (with the determinant clause). R10 is now
`PkgI4.DeRhamComparisonHT` (with the multiplicity-0 clause; `deRhamComparisonHT_iff`). G10's
concrete statement `G10GlueConcrete` and its core `ConjTwistNontrivial` are recorded as
definitions; G10 is part of a glue piece, so neither is a hypothesis.

**Docs.** `docs/research/leaf-fold.md` is the report. `docs/research/h-decomposition.md` has a
Status column in the §2.2 table, the counts, the R10 and R14 notes, and a "Remaining work after
leaf-fold" list.

**Remains:** the 50 open leaves and the ten glue pieces. T14(a′) and T14(b′) could be replaced by
`KummerIndexBound` (`HSyn.t14_of_kummerIndexBound`, compiled; not adopted). The `HDec` wrapper
should go once the file is unified with the kernel port.
