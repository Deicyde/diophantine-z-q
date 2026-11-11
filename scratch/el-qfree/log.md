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

## S2. Multiplier valuation window (VERIFIED by derivation; extends cr3-map-needs L7)
Pole system with multiplier m: A = mB, H = A(A − B²), e, z as in L7. Fix odd p, b = v_p(B), μ = v_p(m).
- Soundness lemma (L7's proof, hypothesis weakened): if b < 0 odd, μ even and μ > b, there is no
  solution. (Proof of L7 uses only a = b + μ odd and a − 2b = μ − b > 0.)
- Completeness constraint at a consumed prime of a genuine instance (b ≥ 1 odd; b = 1 at the slope
  site's P(t)): if μ > b then v_p(θ) = v_p(m(m − B)) = μ + b is odd, p | β, and Loc N β ∧ Loc Nθ β
  fails locally at p (C_{Nθ} has good reduction at p after scaling, a good-reduction point has
  abscissa of even valuation, β has odd valuation). So the prover needs μ < b, i.e. μ ≤ 0 when b = 1.
- Hence any multiplier set M usable at both kinds of input needs v_p(m) ∈ (−1, 1) ∩ 2ℤ = {0} at
  p ∈ P(t) for the chosen m, and v_p(m) ≥ 0 even for all m ∈ M at all p > 324 (soundness for
  b = −1). An input-dependent multiplier m = μ·R₀·B (designed so that v_p(m) > v_p(B) whenever
  v_p(R₀) odd) makes θ = sqf(μR₀(μR₀ − 1)) independent of q but violates the completeness
  constraint at every consumed prime: Φ fails at every genuine instance. Excluded.
- Unbounded k: m = m₀k² needs k ∈ ℤ[1/S] (S = primes ≤ 324) certified by the polynomial. With
  bit encodings k is bounded (each bit is one witness per pole call, ~8.3M variables). An
  existential definition of ℤ[1/S] in ℚ is as hard as the target (ℤ = ℤ[1/S] ∩ ⋂_{p∈S} ℤ_(p), each
  ℤ_(p) diophantine). Quaternion sets T_{a,b} (Poonen 2009, Lemma 2.5: traces of norm-1 elements =
  ⋂_{p∈Δ_{a,b}} ℤ_(p) ∩ real condition) give integrality only at the ramified primes; soundness
  would need Δ_{a,b} ⊇ consumed primes for every witness (a, b), which no fixed choice of b forces
  (primes splitting in ℚ(√b) escape; Chebotarev). STANDARD (Poonen) + derivation.
- Conclusion: M is a finite set {m₀k² : m₀ | ±Π_{p≤324} p, k < 2^K}.
