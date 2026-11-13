# t-different (fleet summary)

**Result.** Two of the three textbook leaves are proved in Lean, sorry-free, over their verbatim
statements from `scratch/h-decomposition/Leaves.lean` (axioms `propext`, `Classical.choice`,
`Quot.sound` only):

* **T20** local form `PkgI6.HilbertDifferentFormula` (I6.7): `PkgI6.hilbertDifferentFormula`,
  `scratch/t-different/HilbertLocal.lean`.  Proof via monogenicity `B = A[x]` (Serre III §6
  Prop. 12, proved here by Nakayama, without completeness), Mathlib's conductor formula
  `𝔇 = (f'(x))`, `f'(x) = ∏_{σ≠1}(x − σx)`, and counting.
* **T21** local form `PkgI6.DifferentBound` (I6.6): `PkgI6.differentBound`,
  `scratch/t-different/DifferentBound.lean`.  Proof: Hensel's lemma in `B` (proved), the
  unramified subfield `K(u)`, Euler's formula, `e f = [L : K]` ⇒ `e ∈ Tr_{B/A}(B)` ⇒ the bound via
  Mathlib's `not_dvd_differentIdeal_of_intTrace_notMem`.

**Not done.** T22 (Herbrand quotient and transitivity, `PkgI6.HerbrandQuotient`,
`PkgI6.HerbrandTransitivity`): statements checked (no defect), not proved; a plan with the Mathlib
inputs is in `docs/research/t-different.md` §4.  The global forms
`GlueConductor.HilbertDifferentFormula` / `SerreDifferentBound` (consumed by `D1_genuine`) are not
proved: the local-to-global transport stays a citation, as h-decomposition.md already allows.

**Compiles.** `lake env lean scratch/t-different/{Statements,HilbertLocal,DifferentBound}.lean`.
Report: `docs/research/t-different.md`; log: `scratch/t-different/log.md`.
