# mcr-quot (2026-11-14)

**Result.** The four glue Props that mcr-glue left under `ModelCoordinateResidue` are proved or
reduced by compiled Lean (`scratch/mcr-quot/MCRQuot.lean`, exit 0, about 27 s, no sorry, standard
axioms):

- **C2 `CoordinateFromSections`** is proved from A (finiteness only) and T5. This includes
  `P1Translate`: translations of `P¹_{ℤ_(p)}` by charts, with the affinity of the new chart and the
  polynomial-ring property proved.
- **A `FibreAutTame`** is proved from T5, `CurveBijIso` (a textbook leaf) and `ModelYIrreducible`.
  - Along the way, `CurveClosedQbarFinite` (dimension theory of relative curves) and the closed
    fixed locus were proved.
  - `ModelYIrreducible` is in turn proved from the decomposition's existing glue
    `CoverModelOfHeckeN` together with T5.
- **C1 `CMSectionsDisjoint`** is proved from A, the same inputs, and one object-level glue Prop,
  `CMStabObj`. The glue (C1c) `StabFixesClosure` is proved by the closed-equalizer argument.
- **B `GenericQuotientP1`** is reduced to `QuotientDescendsMapQ` (descent of an invariant map to
  `P¹`) and `ToP1BijIsCoordinateQ` (the `P¹` case of `CurveBijIso`, stated by charts). The lifting
  of `ℚ̄`-points through the quotient is proved.

Final composite: `MCRQuot.modelCoordinateResidue_final7`. Its inputs are L1–L6, T5,
`CurveBijIso`, `CoverModelOfHeckeN`, `QuotientDescendsMapQ`, `ToP1BijIsCoordinateQ` and
`CMStabObj`.

**Findings.**

- C2 needs the finiteness of `fibreAut`.
- B needs `𝒵` proper and smooth (supplied by L3).
- A and C1 need `Y` irreducible over `ℚ`, which their hypotheses do not give. It is supplied by
  `CoverModelOfHeckeN`.
- Own glue amended: `CurveClosedQbarFinite` needs properness (counterexample: the line with
  infinitely many doubled points).
- No target statement was found false.

**Remains.** Three glue Props:

- `QuotientDescendsMapQ`: sheaf-level descent of invariant sections.
- `ToP1BijIsCoordinateQ`: needs `P¹` as a smooth scheme (Mathlib has `Proj` and its properness)
  and gluing of morphisms.
- `CMStabObj`: needs the normalizer of `ι(𝒪)` in `End A` at CM points.

A model review judged all the open Props true.

Report: docs/research/mcr-quot.md. Log: scratch/mcr-quot/log.md.
