# mobius-glue (fleet summary)

**Result.** qm-pin's `MobiusGlue` (copied verbatim, with the qm-pin definitions it uses) is proved
in Lean from four named facts: `mobiusGlue_of_named : CurveRatFactor → CurveSurj →
ObjBridge.TorsionStructure → AutOInnerFinite → MobiusGlue` (`scratch/mobius-glue/MobiusGlue.lean`;
0 errors; axioms `[propext, Classical.choice, Quot.sound]`).
- `CurveRatFactor`: on a proper smooth curve over ℚ, a map to P¹ constant on the fibres of another
  map σ to P¹ is a rational function of σ at ℚ̄-points (textbook curves, not in Mathlib).
- `CurveSurj`: a map to P¹ with finite ℚ̄-fibres from a proper smooth curve with a ℚ̄-point is onto
  (textbook, Hartshorne II.6.8, not in Mathlib).
- `TorsionStructure`: existing textbook leaf T5.
- `AutOInnerFinite`: Aut(𝒪) modulo conjugation by units is finite (textbook: Skolem–Noether + the
  normalizer of a maximal order).

**Compiled glue.** A rational function injective on an algebraically closed field of characteristic 0
has degree ≤ 1 (Wronskian argument); such a function without finite pole fixing 0 and c ≠ 0 is the
identity (the "Möbius map fixing 0, ∞, −16/27" step); the same-fibre, CM-value and surjectivity
bookkeeping; finitely many level structures per pair from T5 (via the kernel's `Level3.torsor`);
transport of level structures along QM isomorphisms; `TwistClassFinite` from T5 + `AutOInnerFinite`;
downstream `sameTripleMor_of_named`, `pointwise_of_witness_named`.

**Remains.** The two curve facts (true, argued in docs/research/mobius-glue.md §3; need curve theory
Mathlib lacks) and `AutOInnerFinite` (standard; Lean proof would need the normalizer computation).
Report: docs/research/mobius-glue.md.
