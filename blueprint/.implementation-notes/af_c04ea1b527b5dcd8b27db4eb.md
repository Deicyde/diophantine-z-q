# Implementation note: A lower bound for L(1,χ) at real characters

- Owner: not yet assigned (plan step 3.5, after 3.1–3.4; pp-quadfield supplies the residue bound). Namespace `ZInQ.Progressions`; modules import Mathlib (and earlier `Progressions` modules) only.
- Lean name: proposed `ZInQ.Progressions.norm_LFunction_one_ge_of_sq_eq_one`.
- Draft:
  ```lean
  variable {q : ℕ} [NeZero q]
  theorem norm_LFunction_one_ge_of_sq_eq_one {χ : DirichletCharacter ℂ q} (hχ2 : χ ^ 2 = 1)
      (hχ : χ ≠ 1) :
      1 / (40 * (q : ℝ) ^ ((3 : ℝ) / 2)) ≤ ‖χ.LFunction 1‖
  ```
- Mathlib: `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` (class number formula), `riemannZeta_residue_one`, continuity of `χ.LFunction` at `1`, `tendsto_nhds_unique`, `Finset.prod_le_prod`; elementary arithmetic: `(p+1)/(p-1) ≤ p` for `p ≥ 3`, `∏_{p ∣ q} p ≤ q` (`Nat.prod_primeFactors_dvd`).
- The plan gives `c q^(-3/2)` with `c ≈ 1/40`; the proof gives `log φ / 18 ≈ 0.0267 > 1/40`. Writing `q * Real.sqrt q` instead of the real power is fine.
