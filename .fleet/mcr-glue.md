# mcr-glue (2026-11-14): `ModelCoordinateResidue`

**Verdict.** The residue half of the target is proved. The target reduces to the coordinate
alone, `QuotientP1Coordinate`: a finite map `q : 𝒴 → 𝒵` and an isomorphism `ρ' : 𝒵 ≅ P¹_{ℤ_(p)}`
(by charts) such that `ρ' ∘ q` satisfies `CoordFibres`. `QuotientP1Coordinate` reduces in turn,
by compiled plumbing, to six leaves (L1–L6) and four glue Props (A, B, C1, C2):

```lean
MCRGlue.modelCoordinateResidue_of_quotient' : QuotientP1Coordinate → ModelCoordinateResidue
MCRGlue.modelCoordinateResidue_of_leaves'' : ProperCurveAF → FiniteQuotientExists →
  TameQuotientSmooth → SmoothModelOfP1 → TameFixedPointsDisjoint → TameInertiaCyclic →
  FibreAutTame → GenericQuotientP1 → CMSectionsDisjoint → CoordinateFromSections →
  ModelCoordinateResidue
```

**What compiles.** `lake env lean scratch/mcr-glue/MCRGlue.lean` exits 0 in about 20 s.

- The file is `ModelGlue6.lean` verbatim, followed by five parts.
- There is no `sorry` and no `axiom`; the axioms are standard.
- `py/verbatim_check.py` prints ALL OK.

Proved along the way:

- `transcendental_of_polyCharts`: a polynomial-chart map to `P¹`, pulled back along an integral
  morphism, has transcendental residue at every point whose residue field is not algebraic over
  `𝔽_p`.
- `specialFibreTranscendence` (a named glue Prop of step 1, now proved): on a smooth relative
  curve over `ℤ_(p)`, `𝔪_ξ = (p)` implies that `κ(ξ)` is not algebraic over `𝔽_p`. The proof
  goes through the special fibre, Jacobson closedness and the kernel's `smoothStalkDimOne`.

Two sanity checks also compile:

- `isGQuotient_bot_id`: the SGA 1 quotient definition is satisfiable.
- `hecke_mem_fibreAut`: the group contains the Hecke automorphisms.

**The hypotheses do not already contain a coordinate on 𝒴** (docs §1, with an elementary
example). The coordinate must come from the tame quotient and from the disjointness of the CM
sections.

**What remains.**

- **Leaves.** All are stated over genuine definitions: SGA 1 quotient `IsGQuotient`, `Aut`,
  isomorphisms onto `P¹` by charts, closures of points. Locators are UNVERIFIED (no network).
  - L1: proper smooth curves over `ℤ_(p)` are AF (Lichtenbaum).
  - L2: finite quotients exist and are finite (SGA 1 V 1.8).
  - L3: tame quotients are smooth (SGA 1 V / Mumford §7 / EGA IV 17.5.1).
  - L4: a smooth model of `P¹_ℚ` is `P¹_{ℤ_(p)}`.
  - L5: fixed points of tame automorphisms have disjoint closures (Edixhoven 1992 Prop. 3.4).
  - L6: tame inertia is cyclic (Serre, *Local Fields* IV §2).
  - L1, L3 and L6 are textbook composites.
- **Glue, not proved.** Mathlib 4.35 lacks scheme quotients, `P¹` with Möbius maps, and fixed
  schemes.
  - A: `fibreAut` is finite with order dividing 144.
  - B: the generic fibre of the quotient is `P¹_ℚ`.
  - C1: the CM sections are disjoint, from L5 and L6.
  - C2: normalize the coordinate by the three sections.

An independent model review of the Lean statements found no false, vacuous or mis-encoded
Prop. Its four docstring completions were applied. Report: docs/research/mcr-glue.md. Log: scratch/mcr-glue/log.md.
