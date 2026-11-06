# Full-logarithm ratios of multiples of P0 (logarithm-ratio)

- Lean name: `ZInQ.Mult.ellLog_ratio`.
- Draft:
  ```lean
  theorem ellLog_ratio (hMW : MordellWeilE) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (𝔭) (h𝔭)
      (h u : ℤ) (hh : h ≠ 0) (hH : mapPt 𝔭 (h • genP0) ∈ formalNbhd)
      (hU : mapPt 𝔭 (u • genP0) ∈ formalNbhd) :
      ellLog ⟨_, hH⟩ ≠ 0 ∧ (h : K_𝔭) * ellLog ⟨_, hU⟩ = u * ellLog ⟨_, hH⟩
  ```
  (`mapPt 𝔭 = WeierstrassCurve.Affine.Point.map` along `K0 →+* 𝔭.adicCompletion K0`.)
- Mathlib: `WeierstrassCurve.Affine.Point.map` (a group hom), `AddMonoidHom.map_zsmul`.
- FINITE COMPUTATION: no. Difficulty: easy (~60 lines given formal-logarithm).

Shared design (multiplication chapter): namespace `ZInQ.Mult`, files under
`ZInQKernel/Multiplication/`. Points are `genCurve.toAffine.Point` over `K0 = QuadraticAlgebra ℚ 2 0`;
codes are `ZInQ.iota`; template relations are `ZInQ.Syntax.Rel`. Valuations on `K0` at a prime
`𝔭 : IsDedekindDomain.HeightOneSpectrum Zs` (with `Zs` the model chapter's `ℤ[√2]`) are taken as
`ℤ∪{∞}`-valued via `IsDedekindDomain.HeightOneSpectrum.valuation K0 𝔭` (multiplicative, `ℤᵐ⁰`);
a thin wrapper `ZInQ.Mult.vP 𝔭 : K0 → WithTop ℤ` is recommended. The completion is
`𝔭.adicCompletion K0`. The constants `c_*`, `ℓ_0`, `A_ht`, `T` are the syntax chapter's symbolic
`FixedExpr` values and are never evaluated (no `decide`/`norm_num` on them).
