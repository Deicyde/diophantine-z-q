# elkies-print (2026-11-16)

**Result.** The research field `elkiesX6StarFunctionField` is discharged from one new leaf, `ElkiesX6StarEvery`, plus
the moduli witness the bundle already supplies (`gonzalezRotgerX6Ab`). The new leaf is Elkies (ANTS-III 1998 §3;
locator UNVERIFIED) in elkies-coord's function-field form, with the same clauses (`ℚ(X₆)^W = ℚ(t)`, CM values
`t = 0, 1, ∞`, charts). It is stated for every witness of the moduli description of `X₀(6,1)` and makes no existence
claim. That existence claim was the reason for the 11-16 re-rating ("carries the R1 moduli witness").
The leaf is no stronger than the field: `every_of_functionField : ElkiesX6StarFunctionField → TorsionStructure →
ElkiesX6StarEvery` is proved by pinning the witness in Lean. The pinning uses an abelian-scheme fine comparison, a
coarse comparison from T5 + FactorThroughSurj + CurveBijIso, and transport of t, `ℚ(X)^W`, the CM clause and the
charts along the isomorphism. Hence `every_iff_functionField`, given a witness and T5.

**Compiles (VERIFIED).**
* `ZInQKernel/Contrib/OneProof/ElkiesX6StarEvery.lean` (imports only ElkiesX6StarPrinted); standard axioms.
* `#discharges` shows `OpenResearchLeaves28.elkiesX6StarFunctionField` discharged by
  `elkiesX6StarFunctionField_of_every` (assumes ElkiesX6StarEvery, X6WitnessAb) and `..._of_every_gr` (assumes
  ElkiesX6StarEvery, GonzalezRotgerX6Ab).
* Autofold dry-run: strict 16/21 → 17/20, strictest 16/21 → 17/20 (−1 GLUE). The generated `sixContactMin_of_open39`
  compiles with the standard axioms.

**Remains / caveats.**
* The rating of the new leaf as printed form assumes the moduli reading of `X(6)`, `W` and the CM points that every
  X₆ leaf uses. If the 11-16 dictionary ruling on `gonzalezRotgerProp56X6` (CM points read as ℚ̄ pairs) is applied
  here too, the leaf is a consequence and the net change is 0 GLUE (no longer a composite). The reviewer should
  decide.
* Elkies' wording and the 0/∞ orientation are unread (no network).
* Fold order with grx6ab-print: if their fold of `gonzalezRotgerX6Ab` lands first, take the witness from
  `GRX6AbPrint.x6ModuliWitness_of_coarse` (same Prop as `X6WitnessAb`); see report §5.

Report: docs/research/elkies-print.md; scratch: scratch/elkies-print/ (log, spec, dry-run, discharges, axioms).
