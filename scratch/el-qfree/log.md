# el-qfree log

## S1. Quantifier structure of the two consumers (VERIFIED, reading Lean)
- `Test n κ t` (Assembly/Local/SixLocalTests.lean:66): `∃ h s₀ : ℤ, ∃ η q : ℚ`, with only
  `h ≠ 0, h ≠ κ, η² = 1, a₀ ≠ 0, W ≠ 0, Θ ≠ 0, Φ(R/Θ²)`. No real or p-adic condition on q; η is a
  free sign (η = −sign F gives R₀ < 0, B < 0).
- `SlopePred t ℓ c` (Multiplication/Certificate/SlopePredicate.lean:52): `∃ η q h z` with
  `h g ≠ 0, h g ≠ c 0`, nonvanishing, `Φ(R/Θ²)`. q, η, the six shifts h_g and the 18 integers z_g free.
- The open sets U_test, U_slope of cr3-map-needs are imposed only by PC's hypotheses
  (test_complete takes q from poleInput_real). Completeness without PC needs:
  ∃ (η, q, h, s₀) with Φ(B) (test), ∃ (η, q, h_g, z_g) with Φ(B) (slope).
- Test(n, κ, n) itself accepts any κ ≠ 0 (κ deep is used only to verify PC's S₀-valuations).
