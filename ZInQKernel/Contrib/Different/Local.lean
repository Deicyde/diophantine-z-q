/-
Copyright (c) 2026 The Z-in-Q contributors (task t-different; integrated by task diff-bridge).
-/
import Mathlib
import ZInQKernel.HDecomp.Conductor.I6Base
import ZInQKernel.HDecomp.Textbook.Different

/-!
# Local different leaves (T20, T21, T22 local forms), importable

The proofs of task t-different (`scratch/t-different/All.lean`, report
`docs/research/t-different.md`), over the definitions and leaf statements of
`ZInQKernel/HDecomp/Conductor/I6Base.lean`:
`PkgI6.hilbertDifferentFormula : PkgI6.HilbertDifferentFormula` (T20 local, I6.7),
`PkgI6.differentBound : PkgI6.DifferentBound` (T21 local, I6.6),
`PkgI6.herbrandQuotient : PkgI6.HerbrandQuotient` (T22a, I6.8),
`PkgI6.herbrandTransitivity : PkgI6.HerbrandTransitivity` (T22b, I6.9).
No `sorry`, no `axiom`.

Task contrib-clashes (2026-11-17): this file used to repeat, character for character up to line
breaks, the declarations of `ZInQKernel/HDecomp/Textbook/Different.lean` (66 names: the `TDifferent.*`
helpers and `PkgI6.*` results above). Six of them are definitions (`TDifferent.phiF`, `phiExpl`,
`filtR`, `resHom`, `PkgI6.MonogenicDVR`, `PkgI6.TraceContainsRamificationIdx`), and Lean refuses to import
two modules that both declare a definition of the same name, so no file could import both. The module now
re-exports that canonical copy; every name it used to declare is still available, with the same type
and value, to every importer.
-/
