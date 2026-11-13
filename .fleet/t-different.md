# t-different (fleet summary)

**Result.** All three textbook leaves are proved in Lean in their local forms, sorry-free, over the
verbatim statements of `scratch/h-decomposition/Leaves.lean` (axioms `propext`,
`Classical.choice`, `Quot.sound` only; statement identity checked mechanically):

* **T20** `PkgI6.HilbertDifferentFormula` → `PkgI6.hilbertDifferentFormula`
  (`scratch/t-different/HilbertLocal.lean`): monogenicity `B = A[x]` (proved, by Nakayama, no
  completeness), Mathlib's conductor formula `𝔇 = (f'(x))`, `f'(x) = ∏_{σ≠1}(x − σx)`, counting.
* **T21** `PkgI6.DifferentBound` → `PkgI6.differentBound` (`DifferentBound.lean`): Hensel's lemma
  in `B` (proved), unramified subfield `K(u)`, Euler's formula, `e f = [L:K]` ⇒ `e ∈ Tr_{B/A}(B)` ⇒
  the bound via `not_dvd_differentIdeal_of_intTrace_notMem`.
* **T22** `PkgI6.HerbrandQuotient`, `PkgI6.HerbrandTransitivity` → `PkgI6.herbrandQuotient`,
  `PkgI6.herbrandTransitivity` (`Herbrand.lean`): min-formula for `φ`, coset lemma, Serre IV §1
  Prop. 3 from monogenic generators, `|H_0| = e` and the restriction map from Mathlib's
  `IsGaloisGroup` API, IVT for `ψ`.  These are exactly the fields `t22a`, `t22b` of
  `HSyn.TextbookLeaves`.

**Not done.** The global forms `GlueConductor.HilbertDifferentFormula` /
`SerreDifferentBound` (fields `t20`, `t21` of `HSyn.TextbookLeaves`, consumed by `D1_genuine`):
local-to-global transport not in Lean (route sketched in the report §5; T20 and T22 proofs need no
completeness, which helps).

**Compiles.** `lake env lean scratch/t-different/{Statements,HilbertLocal,DifferentBound,Herbrand}.lean`
(6 s, 9 s, 41 s, 17 s).  Report: `docs/research/t-different.md`; log: `scratch/t-different/log.md`.
