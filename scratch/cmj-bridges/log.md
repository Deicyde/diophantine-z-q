# Results

- VERIFIED (repository): the clean base is `b64a5639575bdb655ba5e2f8e1779ef84a4a1f35`.
  `cmjDegree` is GLUE in both columns; the H part has 29 rows (4 LEAF / 25 GLUE).
- VERIFIED (manuscript): L584–587 use a CM elliptic curve over the bounded-degree field,
  the discriminant of its full geometric endomorphism order, and the degree of its j-invariant.
  STANDARD (published, exact locator): the supplied human reading of Fowler §2·1, p. 613
  (fork issue #14, comment 6973419601) gives the equality over ℚ; p. 612 gives its
  primitive-equation discriminant. No independent PDF reading was performed.
- VERIFIED (Lean): `CMjBridgesPrint.lean` compiled with `lake env lean`. The printed
  `CMjDegreePrint` uses the lattice j-value, the actual primitive equation of a
  quadratic upper half-plane period, and Fowler's proper ideal class number.
  `modularJ_eq` validates the classical normalization.
- VERIFIED (Lean): `CMjBridgesArithmetic.lean` and `CMjBridgesDiscriminant.lean` compiled
  with `lake env lean`. Coefficient base change maps algebraic j; membership in the
  image field gives the degree inequality. The proper ideal count identifies the Picard
  cardinal. Primitive period coefficients compute the multiplier ring and its discriminant.
- VERIFIED (Lean): `CMjBridgesPeriods.lean` compiled with `lake env lean`. The proved
  torsion count, coordinate uniformization, GAGA for maps and rigidity supply the actual
  complex base change and its period with discriminant `orderDisc R`.
- VERIFIED (library interfaces): the point and scheme uniformization interfaces do not
  produce a field of definition for the modular j of this period. Mathlib's coefficient
  j-value requires a Weierstrass equation; no proved comparison for the scheme curve was found.
- VERIFIED (Lean): `CMjBridges.lean` compiled with `lake env lean`.
  `cmjDegree_of_print_of_periodJDescends` proves the live row from the printed
  equality conditional on `CMPeriodJDescends`. The latter is only the field-of-definition
  comparison for the analytic j of the actual CM period; it is open glue.
- VERIFIED (Lean): `lake env lean scratch/cmj-bridges/Axioms.lean` passed.
  The original group-model uniformization interface and normalized modular j surjectivity
  both follow from existing proofs. All 15 new theorems (including the two scratch checks)
  and the reused Picard class-number theorem use only the standard axioms.
- VERIFIED (Lean): `lake env lean scratch/cmj-bridges/Discharges.lean` checked the live
  headline (33 open hypotheses). The new candidate discharges `OpenResearchLeaves66.cmjDegree`
  only from `CMPeriodJDescends` and `CMjDegreePrint`.
- VERIFIED (dry run): on 29 H rows, both counts remain 4 LEAF / 25 GLUE. The read-only
  autofold preview projects 5 LEAF / 24 GLUE with a future proof of the open comparison.
  The listed proof name for that comparison is a placeholder; nothing was folded.
