import ZInQKernel.Contrib.R10.Glue
import ZInQKernel.Contrib.AbVarBC.Main

/-!
# G9 closed: from the amended R10 alone

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task r10-amend, 2026-11-13).

Task g9-abvarbc proved `G9Bridge.AbVarBaseChange` outright (`ZInQ.Contrib.AbVarBC.abVarBaseChange`,
`ZInQKernel/Contrib/AbVarBC/Main.lean`). With `Glue.lean`, glue step G9 needs only the amended
leaf `DeRhamComparisonHT`:

* `g9GlueHT : G9GlueHT` — g0-mod-galois's `G9Glue` with R10 replaced by the amended leaf (T23
  dropped), proved outright;
* `g9GlueHT' : G9GlueHT'` — the same with T23 kept (`G9Glue` with R10 amended);
* `g9Glue_of_deRhamComparisonHT : DeRhamComparisonHT → G9Glue` — the verbatim `G9Glue`.
-/

namespace ZInQ.Contrib.R10

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.G0Galois

/-- **G9, closed**: `G9Glue` with its R10 hypothesis replaced by the amended leaf
`DeRhamComparisonHT`, with no other hypothesis. -/
theorem g9GlueHT : G9GlueHT :=
  g9GlueHT_of_abVarBaseChange ZInQ.Contrib.AbVarBC.abVarBaseChange

/-- `G9Glue` verbatim with R10 replaced by the amended leaf (T23 kept as an unused hypothesis). -/
theorem g9GlueHT' : G9GlueHT' :=
  g9GlueHT'_of_g9GlueHT g9GlueHT

/-- g0-mod-galois's `G9Glue` (verbatim) from the amended R10. -/
theorem g9Glue_of_deRhamComparisonHT (h : DeRhamComparisonHT) : G9Glue :=
  g9Glue_of_HT ZInQ.Contrib.AbVarBC.abVarBaseChange h

end ZInQ.Contrib.R10

#print axioms ZInQ.Contrib.R10.g9GlueHT
#print axioms ZInQ.Contrib.R10.g9GlueHT'
#print axioms ZInQ.Contrib.R10.g9Glue_of_deRhamComparisonHT
