# Valuations of the normalization at an odd contact prime (contact-valuations)

- Lean name: `ZInQ.Mult.contact_valuations`.
- Draft:
  ```lean
  theorem contact_valuations (t η q : ℚ) (ht : t ∉ contactSet) (ht1 : t ≠ 1) (hη : η = 1 ∨ η = -1)
      (ha : 1 - η * contactPoly t / (t-1)^8 * q^2 ≠ 0) (p : ℕ) (hp : p.Prime) (hpSb : p ∉ S_b)
      (c : ℚ) (hc : c ∈ contactSet) (hk : 0 < padicValRat p (t - c)) (hodd : Odd (padicValRat p (t - c))) :
      padicValRat p (η * contactPoly t / (t-1)^8) = padicValRat p (t - c) ∧
      Odd (padicValRat p R) ∧ padicValRat p R ≤ padicValRat p (t - c)
  ```
- Mathlib: `padicValRat.add_eq_min`, `padicValRat.mul`, `padicValRat.div`, `padicValRat.pow`;
  `p > 61` from `p ∉ S_b`. Upstream `ZInQ.ValuationObstruction` has similar `padicValRat`
  bookkeeping patterns (guarded nonvanishing).
- FINITE COMPUTATION: no (the contact differences `|c - c'| ≤ 60`, `|c - 1| ≤ 61` are `decide` over the
  21 pairs). Difficulty: easy-medium (~150 lines).

Shared design (multiplication chapter): namespace `ZInQ.Mult`, files under
`ZInQKernel/Multiplication/`. Points are `genCurve.toAffine.Point` over `K0 = QuadraticAlgebra ℚ 2 0`;
codes are `ZInQ.iota`; template relations are `ZInQ.Syntax.Rel`. Valuations on `K0` at a prime
`𝔭 : IsDedekindDomain.HeightOneSpectrum Zs` (with `Zs` the model chapter's `ℤ[√2]`) are taken as
`ℤ∪{∞}`-valued via `IsDedekindDomain.HeightOneSpectrum.valuation K0 𝔭` (multiplicative, `ℤᵐ⁰`);
a thin wrapper `ZInQ.Mult.vP 𝔭 : K0 → WithTop ℤ` is recommended. The completion is
`𝔭.adicCompletion K0`. The constants `c_*`, `ℓ_0`, `A_ht`, `T` are the syntax chapter's symbolic
`FixedExpr` values and are never evaluated (no `decide`/`norm_num` on them).
