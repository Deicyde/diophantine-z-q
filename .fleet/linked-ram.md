# linked-ram (fleet summary)

**Result.** Both GLUE fields that g0-assemble3 left for `LinkedRam` (`GluePieces4` fields 45 `kernelFieldBreaks`,
46 `tateRamAtThree`) are gone. `LinkedRam` now rests on G3 (proved), the research/textbook leaves R6 and T5 already in
the bundles, one textbook leaf candidate `UpperBreakBound` (absolute upper breaks of a degree-`a` extension of ℚ_p are
`< 4a²`; manuscript L796-811 from Serre III §6, IV §1-3), and one glue Prop `BetaSignAtTwo` (the sign of `β` on high
upper groups at 2; needs local CFT). New bundle `HSyn.GluePieces5` (44 fields = 14 LEAF + 4 LEAF? + 26 GLUE, against
46 = 14 + 3 + 29) with `HSyn.sixContactMin_of_leaves5`; it also folds lt-goodred's proofs of `goodRedTorsion`,
`qmEndRank`.

**Finding F1.** `GluePieces4.tateRamAtThree` is not quantified over `G7Data`, so g0-assemble3's `[L:ℚ] ≤ D` fix does not
reach it (likely false for unbounded `K`, SPECULATIVE). Replaced by `TateRamAtThreeD` (with `finrank ℚ L ≤ D`), which
is then proved: `tateRamAtThreeD_of_leaves r.r6 t.t5 upperBreakBound` (5-torsion field of degree ≤ |GL₄(𝔽₅)| = G₀,
break bound, Raynaud over it, wild ⇒ unipotent action trivial).

**Proved outright** (no hypotheses): `KernelFieldBreaksHigh` (clause p > D, via an elementary theory of wild
elements of G_{ℚ_p}: W1-W5), `UpperAbsWild` (G^u ⊆ P for u > 0, Herbrand-function estimates), `TorsionFieldFive` from
T5, `χ(decomp₂ σ) = 1` on high upper groups.

**Compiles** (VERIFIED, Lean 4.35 / Mathlib 4.35, standard axioms only): `scratch/linked-ram/olean/Tail.lean` over
g0-assemble3's olean chain + lt-goodred (0 errors); `test/Wild.lean` (Mathlib only); flat file
(g0-assemble3 + lt-goodred + Tail, 93 294 lines): exit 0 in 945 s, 0 errors, 244 standard axiom reports
(`scratch/linked-ram/flat_summary.txt`).

**Remains.** `BetaSignAtTwo` (GLUE), `UpperBreakBound` (LEAF?, for the literature list), `LinkedFrob` (not this task).
Report: `docs/research/linked-ram.md`; log: `scratch/linked-ram/log.md`.
