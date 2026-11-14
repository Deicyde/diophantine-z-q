# mcr-quot (2026-11-14)

**Result.** All four glue Props that mcr-glue left under `ModelCoordinateResidue` are proved by
compiled Lean from leaves plus **two** remaining glue Props (`scratch/mcr-quot/MCRQuot.lean`,
exit 0, about 30 s, no sorry, 54 `#print axioms` all standard):

- **C2 `CoordinateFromSections`** is proved from A and T5. This includes `P1Translate`:
  translations of `P¹_{ℤ_(p)}` by charts, with the new chart affine and the polynomial-ring
  property proved.
- **A `FibreAutTame`** is proved from T5, the textbook leaf `CurveBijIso` and `ModelYIrreducible`.
  Along the way the fixed locus was shown closed and `CurveClosedQbarFinite` (dimension theory of
  relative curves) was proved. `ModelYIrreducible` is itself proved from the decomposition's
  existing glue `CoverModelOfHeckeN` together with T5.
- **C1 `CMSectionsDisjoint`** is proved from A, the same inputs, and `CMStabObj`, an object-level
  statement on CM classes with no schemes in it. (C1c) `StabFixesClosure` was proved through the
  closed equalizer.
- **B `GenericQuotientP1`** is proved from A, T5, L3 and `ToP1BijIsCoordinateQ` (the `P¹` case of
  `CurveBijIso`, stated by charts). (B-desc) is fully proved: invariant sections and maps to `P¹`
  descend through SGA 1 quotients, and `ℚ̄`-points lift through them.

Final composite: `MCRQuot.modelCoordinateResidue_final8`. Its inputs are L1–L6, T5,
`CurveBijIso`, `CoverModelOfHeckeN`, `ToP1BijIsCoordinateQ` and `CMStabObj`.

**Findings.**

- C2 needs the finiteness of `fibreAut`.
- B needs `𝒵` proper and smooth (supplied by L3).
- A and C1 need `Y` irreducible over `ℚ`, which their hypotheses do not give; it comes from
  `CoverModelOfHeckeN`.
- Own glue amended: `CurveClosedQbarFinite` needs properness (counterexample: the line with
  infinitely many doubled points).
- No target statement was found false.
- A model review judged all the open Props true.

**Remains.**

- `ToP1BijIsCoordinateQ` needs `P¹` as a smooth scheme (Mathlib has `Proj` and its properness)
  and gluing of morphisms.
- `CMStabObj` needs the normalizer of `ι(𝒪)` in `End A` at CM points.

Report: docs/research/mcr-quot.md. Log: scratch/mcr-quot/log.md.
