# r17-rebase (fleet summary)

**Verdict.** On current main (c0f3d085, leaf-fold33), `r17 : LadicCond.CarayolR17'` is replaced by one printed leaf,
`CarayolPrinted.CarayolThmAIrr`. The fold dry run gives strict and strictest **11/18 on 29 → 12/17 on 29 (GLUE −1)**, with
the leaf flagged unread plus the reading risk. The generated module and a frozenTarget variant compile with the standard
axioms only.

**What compiles (VERIFIED, Lean 4.35 / Mathlib v4.35).**
* r17-print's `CarayolPrinted.lean`, `NewformDict.lean` and `CarayolLevel.lean` build on the merged tree with no edits.
* New: `ZInQKernel/Contrib/OneProof/CarayolPrintedIrr.lean`. It proves the Burnside step: from irreducible plus odd
  (an involution with det −1) to "the image spans M₂", `adjoin_eq_top_of_irreducible_odd`. The leaf is therefore stated
  with Ribet's plain irreducibility and oddness: `carayolThmA_of_irr`, `carayolR17'_of_printedIrr`. The conductor
  clause is split off as `CarayolExistence` + `CarayolConductor` (`carayolR17'_of_split`).
* `#discharges` against main: `OpenResearchLeaves31.r17` by `carayolR17'_of_printedIrr`, still assuming
  [CarayolThmAIrr, EigenformCoeffFieldFinite], standard axioms.
* Clash check: 243 of main's 244 top-level Contrib modules together with the new modules elaborate. The 244th
  (`ZInQKernel.Contrib.AllContrib`) already clashes with HDecomp on main (`PkgI6.TraceContainsRamificationIdx`),
  and none of the 71 new names occurs in it.
* Scenario F: `carayolRealization_of_printed` proves modular-split's `CarayolRealization` (verbatim copy), so the
  leaf supersedes that split too.

**Rating.** Four clauses are printed: existence, traces, irreducible, odd. The Burnside form was a step beyond the
print; it is now proved in Lean. The conductor clause is beyond Théorème (A) as printed: it needs Casselman 1973,
per the audit's row R17. It cannot be proved in Lean today (π_p is not definable), so it is split off as
`CarayolConductor` (composite). The leaf keeps the packaged clause (DDT 1997 Thm 3.1 / Carayol §0.8, UNVERIFIED).
If the statement check rejects the packaging, the leaf goes to pending reading (count unchanged) or the split is
folded (12/18 on 30).

**What remains.** The statement check (docs/research/r17-rebase.md §4.2), the fold by the integrator (recipe in §6,
spec scratch/r17-rebase/autofold.json), and the locators row.
