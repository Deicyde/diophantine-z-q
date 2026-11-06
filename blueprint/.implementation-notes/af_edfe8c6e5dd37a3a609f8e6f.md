# Units of Z[√2] (units)

- Lean names: `ZInQ.Zs_unit_eq`, `ZInQ.Zs_unit_sqClass`, `ZInQ.isSquare_of_totallyPositive_unit`.
- Draft:
  ```lean
  theorem Zs_unit_eq (u : Zsˣ) : ∃ (k : ℤ) (σ : ℤˣ), (u : Zs) = σ * epsZ ^ k  -- epsZ : Zsˣ := 1 + ω
  theorem isSquare_of_totallyPositive_unit (u : Zsˣ) (h : TotallyPositive (u : K0)) : IsSquare u
  ```
- Mathlib: `QuadraticAlgebra.isUnit_iff_norm_isUnit` (Basic.lean); `Mathlib/NumberTheory/Pell.lean`
  (`Pell.Solution₁`, `Pell.IsFundamental`, `Pell.IsFundamental.eq_pow_of_nonneg`) could give the
  norm-one units, but the direct argument in the article (bounding a unit in [1, 1+√2)) is short.
  Units of ℤ[√2] are not in Mathlib in this form.
- FINITE COMPUTATION: a four-candidate check inside the proof (a, b ∈ {0,1}); handled by `decide`
  or `omega`, not worth a separate certificate.
- Difficulty: medium.
