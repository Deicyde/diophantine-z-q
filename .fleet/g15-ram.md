# g15-ram (G15RamG, conductor exponents (i)-(ii))

**Verdict.** `G15RamG D u` (verbatim from scratch/g0-mod-newform) is a predicate on bare data
`D : ModData L A` and is false for arbitrary `D`, so it is a claim about G8's construction. It is
now **proved in Lean from smaller Props**: `G15Ram.g15RamG_of_dvrModel` derives it from
(a) one closed local-field transport `LadicDVRModel` (the DVR model `ℤ_p → 𝓞_F` of a finite
Galois `F ⊆ ℚ̄_p`, with matched ramification groups), (b) `LocalData p r` on `D` (G7/G8 + R6 + D2
+ T16/D3: on `G_F ∩ P_p` the rep is a scalar `β(σ)`, with `e(F) ≤ (DG₀)!` at `p ≤ D` or `F` tame
at `p > D`, plus bounds for the character `β`), and (c) G11's output `G11Out T r` (proved by
g0-mod-galois's `g11`).

**Proved (no sorry, axioms propext/Classical.choice/Quot.sound, VERIFIED):** the break bound
`G^t_{ℚ_p} ⊆ G_F` for `t > 4a²` when `e(F) ≤ a!` (from T20+T21, i.e. the kernel's
`PkgI6.hilbertDifferentFormula`, `PkgI6.differentBound`, through `LadicDVRModel`); positive upper
groups are wild (`upperWild`, unconditional); wild inertia fixes tame extensions (`wildFixTame`,
unconditional, via an averaging argument); the reduction; and `modularConstituent_tail_R`
(g0-mod-newform's tail with `G15RamG` replaced by these pieces, in `Tail.lean`).

**Compiles:** `lake env lean scratch/g15-ram/G15Ram.lean` (~10 s) and
`scratch/g15-ram/Tail.lean` (assembled by `build_tail.sh`, ~40 s), both 0 errors.

**Remains:** `LadicDVRModel` (Mathlib transport, medium); the `D`-side Props, which need G8's
`r_ℓ = β⁻¹ a_σ μ_σ σ` as a Lean object (not yet defined anywhere). At `p > D`, `LargePrimeData`
is essentially clause (ii) itself. Report: docs/research/g15-ram.md; log: scratch/g15-ram/log.md.
