# mcr-quot (2026-11-14)

**Result.** All four glue Props that mcr-glue left under `ModelCoordinateResidue` are proved by
compiled Lean from leaves, one existing glue Prop and **two** new glue Props (`scratch/mcr-quot/MCRQuot.lean`,
exit 0, about 30 s, no sorry, 57 `#print axioms` all standard):

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
- **B `GenericQuotientP1`** is proved from A, T5, L3, `CurveBijIso` and `P1SchemeQ`. The last says
  that the projective line over `ℚ` exists, is proper and smooth, and represents maps to `P¹` by
  charts. (B-desc) is fully proved: invariant sections and maps to `P¹` descend through SGA 1
  quotients, and `ℚ̄`-points lift through them. The `P¹` case of `CurveBijIso`, stated by charts,
  is proved from `CurveBijIso` and `P1SchemeQ`.

Final composite: `MCRQuot.modelCoordinateResidue_final9`. Its inputs are L1–L6, T5,
`CurveBijIso`, `CoverModelOfHeckeN`, `P1SchemeQ` and `CMStabObj`.

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

- `P1SchemeQ` (foundations) needs `Proj ℚ[X₀, X₁]` with its charts, its smoothness and gluing of
  morphisms; Mathlib has `Proj` and its properness.
- `CMStabObj` needs the normalizer of `ι(𝒪)` in `End A` at CM points.

Report: docs/research/mcr-quot.md. Log: scratch/mcr-quot/log.md.
