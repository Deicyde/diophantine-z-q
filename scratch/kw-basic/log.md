# kw-basic results log

- 17:55 start. Plan: move the Mathlib-only declarations of Contrib/KroneckerWeber/Leaves.lean
  verbatim (same namespace, same names) into Basic.lean, add `KroneckerWeberCyclic` /
  `kroneckerWeber_cyclic` there; Leaves.lean imports Basic and proves the HDecomp statements by
  `Iff.rfl`. Downstream names (scratch/h-decomposition/Leaves.lean uses `kroneckerWeberCyclic`,
  `hSynKroneckerWeber`, `HSynKroneckerWeber`) unchanged.
- Tau Ceti closure of the TC KW module: 939 modules besides itself (task expected 5: the old
  `import`-only regex misses `public import`; see tc-closure.txt).
- Seeded TauCeti and HDecomp oleans from ../leaf-fold4 (cp -an, reflink).
- 17:58 `lake build ZInQKernel.Contrib.KroneckerWeber.Basic`: success (5261 jobs, Basic 36 s).
- 17:59 `lake build ZInQKernel.Contrib.KroneckerWeber.Leaves`: success (9990 jobs, Leaves 31 s).
- 17:59 `lake env lean scratch/kw-basic/Check.lean`: the six theorems depend only on propext,
  Classical.choice, Quot.sound (check-output.txt).
- Importers of the changed files: no module under ZInQKernel/ imports Contrib/KroneckerWeber/*;
  the one importer is scratch/h-decomposition/Leaves.lean. Built its imports (10474 jobs, ok), then
  `lake env lean scratch/h-decomposition/Leaves.lean`: 0 errors, no sorry, 9 min 28 s; the
  `#hdec_same` checks of TSkolemKW.KW.KroneckerWeberCyclic and HSyn.KroneckerWeber still report
  "verbatim".
