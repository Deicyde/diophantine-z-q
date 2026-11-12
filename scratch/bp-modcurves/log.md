# bp-modcurves results log

- 11:45 `Gamma1Genus.lean`: defs `pmSubgroup`, `Cosets`, `belyiDeg`, `nu2`, `nu3`, `nuInf`, `genus` over
  Mathlib `SL(2,ℤ)`, `Gamma1`, `ModularGroup.S/T`. Theorems `nu2_Gamma1` (N ≥ 3: ν₂ = 0),
  `nu3_Gamma1` (N ≥ 4: ν₃ = 0), `genus_Gamma1` (N ≥ 4: g = 1 + μ/12 − ν∞/2), `belyiDeg_Gamma1_le`
  (μ ≤ N²), `genus_Gamma1_le` (g ≤ N²), `index_Gamma1_le` (copied from glue-assembly).
  `lake env lean`: exit 0, no errors, no warnings; axioms propext, Classical.choice, Quot.sound. VERIFIED.
