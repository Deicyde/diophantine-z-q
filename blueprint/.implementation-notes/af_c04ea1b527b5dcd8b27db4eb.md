# Implementation note: A lower bound for L(1,χ) at real characters

- Owner: pp-final (plan step 3.5). Namespace `ZInQ.Progressions`; modules under `ZInQKernel/Progressions/`, importing Mathlib and the delivered `Progressions` modules only.
- Lean name: proposed `ZInQ.Progressions.norm_LFunction_one_ge_of_sq_eq_one`.
- Draft:
  ```lean
  variable {q : ℕ} [NeZero q]
  theorem norm_LFunction_one_ge_of_sq_eq_one {χ : DirichletCharacter ℂ q} (hχ2 : χ ^ 2 = 1)
      (hχ : χ ≠ 1) :
      1 / (40 * (q : ℝ) ^ ((3 : ℝ) / 2)) ≤ ‖DirichletCharacter.LFunction χ 1‖
  ```
  Writing `q * Real.sqrt q` instead of the real power is fine; the article says `q^{3/2}`.
- Delivered inputs (all in `ZInQ.Progressions`):
  - classification: `exists_legendre_of_real_char_dvd` (gives `Squarefree d`, `d ≠ 1`, `d.natAbs ∣ q`, `χ p = legendreSym p d` for primes `p ∤ 2q`, primality as `[Fact p.Prime]`);
  - the field: `Qsqrt d`, with `haveI : Fact (¬ IsSquare (d : ℚ)) := ⟨Qsqrt.not_isSquare_of_squarefree hd h1⟩`; `Qsqrt.finrank` (the hypothesis `h2`), `Qsqrt.sqrtInt` and `Qsqrt.sqrtInt_sq` (the `α` and `hα`); `¬ IsSquare d` over `ℤ` from `¬ IsSquare (d : ℚ)` by `Rat.isSquare_intCast_iff`;
  - factorization: `dedekindZeta_eq_riemannZeta_mul_LSeries_mul_prod_of_legendreSym` (needs `q ≠ 0`, `hdq : ∀ p, p.Prime → ¬ p ∣ 2 * q → ¬ (p : ℤ) ∣ d`, which follows from `d.natAbs ∣ q`, and `hχ` from the classification); it is stated with `LSeries (fun n ↦ χ n) s`, convert with Mathlib's `DirichletCharacter.LFunction_eq_LSeries`;
  - local signs: `localEps_mem`, `IdealCount.norm_localEps_le_one`, `IdealCount.norm_natCast_cpow_neg_lt_one` (denominators `1 − ε_p p^{-s}` are nonzero for `0 < re s`);
  - residue: `dedekindZeta_residue_ge` (`log((1+√5)/2) / (6 √|d|) ≤ dedekindZeta_residue (Qsqrt d)`), `log_golden_pos`; with `|d| ≤ q` use `Real.sqrt_le_sqrt`.
- Mathlib: `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` (class number formula, a limit along `𝓝[>] 1` of real `s`), `riemannZeta_residue_one` (along `𝓝[≠] 1`, restrict to `𝓝[>] 1`), `DirichletCharacter.differentiable_LFunction` (continuity at `1` for `χ ≠ 1`), `tendsto_nhds_unique`; elementary arithmetic: `(p+1)/(p-1) ≤ p` for `p ≥ 3`, `∏_{p ∣ q} p ≤ q` (`Nat.prod_primeFactors_dvd`).
- The proof gives `log φ / 18 ≈ 0.0267 > 1/40`.
