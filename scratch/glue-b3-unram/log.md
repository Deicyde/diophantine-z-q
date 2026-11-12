# glue-b3-unram results log

## Unram.lean (self-contained, `import Mathlib`)
- Defs: `LiesOver w p := w.valuation p < 1`; `inertiaGQ w := (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype`;
  `GalUnramifiedOutside L' T` (every `I_w`, `w | p ∉ T`, fixes `L'`); `legChar p`, `etaP p` (Legendre char via `cyc p`).
- Leaves (def : Prop): `LeafB3a` (unique loc. const. quadratic char of `I_w`, p odd), `LeafB3b` (`etaP p` nontrivial on every `I_w`, `w | p` odd),
  `LeafConj` (places over p conjugate, σ⁻¹ I_{w'} σ ≤ I_w), `LeafFinRam` (open H ⊇ I_w for all but finitely many p).
- Glue stated: `CycUnram` (cyc N trivial on I_w for p ∤ N).
- `unramified_outside_of_leaves`: COMPILED (2026-11-11 ~00:00), axioms [propext, Classical.choice, Quot.sound].
- `cycUnram : CycUnram`: PROVED (residue-field argument: `ζ = s(t)/t` has residue 1; if `ζ ≠ 1`, `∑_{i<N} ζ^i = 0` reduces to `N = 0` in the residue field, impossible as `p ∤ N`). Axioms [propext, Classical.choice, Quot.sound].
- `unramified_outside` (main theorem from the four leaves only): COMPILED, axioms [propext, Classical.choice, Quot.sound]. Unram.lean 511 lines, `lake env lean` ~10 s.
