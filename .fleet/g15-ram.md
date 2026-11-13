# g15-ram (G15RamG, conductor exponents (i)-(ii))

**Verdict.** `G15RamG D u` (copied verbatim from scratch/g0-mod-newform) is a predicate on bare
data `D : ModData L A`. It is false for arbitrary `D`, so it is really a claim about G8's
construction.

**Main result.** All the local-field theory in G15 is now proved in Lean.
`G15Ram.g15RamG_of_localData` derives `G15RamG D u` from two inputs on the same `D`:
- `LocalData p r`: on `G_F ∩ P_p` the representation is a scalar `β(σ)`, where `e(F) ≤ (DG₀)!`
  at `p ≤ D` and `F` is tame at `p > D`, plus bounds for the character `β`. This is glue on
  G7/G8 together with R6 + D2 and T16/D3.
- G11's output `G11Out T r`, which g0-mod-galois proves as `g11`.

**Proved (no sorry; axioms propext, Classical.choice, Quot.sound; VERIFIED):**
- the break bound `G^t_{ℚ_p} ⊆ G_F` for `t > 4a²` when `e(F) ≤ a!`, from T20 + T21 (the
  kernel's `PkgI6.hilbertDifferentFormula` and `PkgI6.differentBound`), applied to the DVR model
  `ℤ_p → 𝓞_F = integralClosure ℤ_p F`;
- that model itself (`ladicDVRModelZp`: DVR, finite, torsion-free, Galois fraction fields,
  `PkgI6.lowerRam` matched with `LadicCond.ramSet`);
- positive upper groups are wild (`upperWild`);
- wild inertia fixes tame extensions (`wildFixTame`, by an averaging argument);
- `modularConstituent_tail_R`: g0-mod-newform's tail with `G15RamG` replaced by these pieces,
  with no new local-field hypothesis;
- a non-vacuity check: `LocalData` holds for the trivial representation (`localData_trivRep`).

**Compiles:** `lake env lean scratch/g15-ram/G15Ram.lean` (about 15 s) and
`scratch/g15-ram/Tail.lean` (assembled by `build_tail.sh`, about 40 s); both give 0 errors.

**Remains:** only the `D`-side Props, which need G8's `r_ℓ = β⁻¹ a_σ μ_σ σ` as a Lean object (it
is not defined anywhere yet). At `p > D`, `LargePrimeData` is essentially clause (ii) itself.

Report: docs/research/g15-ram.md. Log: scratch/g15-ram/log.md.
