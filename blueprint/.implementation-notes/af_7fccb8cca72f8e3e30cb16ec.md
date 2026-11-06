# Semantics of the height certificate template (height-certificate-semantics)

- Lean name: `ZInQ.Mult.heightCertificate_rel_iff`.
- Draft:
  ```lean
  theorem heightCertificate_rel_iff (hMW : MordellWeilE) (Y : Fin 3 → Fin 5 → ℚ) (ℓ : ℚ) (c : Fin 4 → ℤ) :
      Syntax.Rel Syntax.heightCertificateTemplate.denote 36 35106 (codes Y ++ ![ℓ] ++ shiftCodes c) ↔
        ∃ n : Fin 3 → ℤ, (∀ i, Y i = iota (n i)) ∧
          ∃ (a : Fin 3 → Fin 2 → ℚ) (b : Fin 3 → ℚ), (∀ i, b i ≠ 0 ∧ ∀ j, b i * Y i j.succ = a i j) ∧
          ∀ k : Fin 9, ∃ s : Fin 3 → ℚ, ∑ l, s l = nine a b k ∧ ∀ l, SlopePred (s l) ℓ c
  ```
- FINITE COMPUTATION: no. Difficulty: medium (~200 lines).

Shared design (multiplication chapter): namespace `ZInQ.Mult`, files under
`ZInQKernel/Multiplication/`. Points are `genCurve.toAffine.Point` over `K0 = QuadraticAlgebra ℚ 2 0`;
codes are `ZInQ.iota`; template relations are `ZInQ.Syntax.Rel`. Valuations on `K0` at a prime
`𝔭 : IsDedekindDomain.HeightOneSpectrum Zs` (with `Zs` the model chapter's `ℤ[√2]`) are taken as
`ℤ∪{∞}`-valued via `IsDedekindDomain.HeightOneSpectrum.valuation K0 𝔭` (multiplicative, `ℤᵐ⁰`);
a thin wrapper `ZInQ.Mult.vP 𝔭 : K0 → WithTop ℤ` is recommended. The completion is
`𝔭.adicCompletion K0`. The constants `c_*`, `ℓ_0`, `A_ht`, `T` are the syntax chapter's symbolic
`FixedExpr` values and are never evaluated (no `decide`/`norm_num` on them).
