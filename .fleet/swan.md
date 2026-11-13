# swan: SwanIndependent, SwanIntegral, AdaptedExists

**Verdict: all three glue Props are proved in Lean, unconditionally, with their statements unchanged.**
`Swan.swanIndependent_proved (p)`, `Swan.swanIntegral_proved` and `Swan.adaptedExists_proved (p)` have exactly
the types `LadicCond.SwanIndependent`, `LadicCond.SwanIntegral` and `LadicCond.AdaptedExists` (kernel
`ZInQKernel/HDecomp/Conductor/LadicCond.lean`). These are the hypotheses `hSw`, `hL8`, `hAd` of g0-mod-newform's
`modularConstituent_tail_G`, and they also make `CarayolR17 ↔ CarayolR17'` unconditional. VERIFIED:
`lake env lean scratch/swan/All.lean` exits 0 with 0 errors, no sorry, about 35 s; axioms
[propext, Classical.choice, Quot.sound].

How:
- `AdaptedExists`: an elementary proof from Mathlib alone (`Swan.lean` §1-§4), needing neither Baire nor
  lattices. Wild elements have p-power order on every finite Galois level (trace trick:
  T x = Σ δ^j x preserves norms, so it is bijective). For ℓ ∤ m, ‖((1+A)^m − 1)_ij‖ = ‖A_ij‖ at the largest
  entry. Continuity plus the Krull topology gives the level.
- `SwanIntegral` and `SwanIndependent` follow from Herbrand's theorem (`Swan.swan_main`), through three
  Props, all proved: H1, the finite-level change of variables Sw_L = ∫ codim V^{G^u(L)∩P}; H2,
  G^u ⊆ P for u > 0; H3, G^u → G^u(L) is onto (Herbrand plus compactness of G_{ℚ_p}).
- Herbrand over LadicCond's definitions is derived from the kernel leaf I6.8 `PkgI6.HerbrandQuotient`
  (`Bridge.lean`). The rings of integers 𝓞_E ⊆ ℚ̄_p are shown to be DVRs, finite over ℤ_p and Galois at the
  FractionRing level, with `galRestrict`, and lowerRam/herbrandPhi/upperRam are matched with
  ramSet/phiAt/upperSet. I6.8 itself is t-different's proof, copied into All.lean; the kernel's I6Base
  definitions are character-for-character the same.

What compiles: `scratch/swan/Swan.lean` (1020 lines), `Bridge.lean` (468 lines) and `All.lean` (2713 lines,
from `build.sh`). The last one is the self-contained unconditional file.

What remains: integration only. All.lean imports just the kernel's `LadicCond` and `I6Base`, so it can become
kernel modules (t-different's TDifferent part, then Swan, Bridge, final_part). `Bridge.lean` is the first
concrete instance of the pkg-I6 DVR leaves at 𝓞_E ⊆ ℚ̄_p, and should transport I6.6/I6.7 the same way.
Report: docs/research/swan.md.
