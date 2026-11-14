# shimura-glue results log

## Setup
- `.lake/build`, `lean/.lake/build` reflink-copied from ~/dzq-check2 (commit 5da857b0; only
  `ZInQKernel/OneProof/TYZSplit.lean` differs from this base, docstring only).

## Step 1: Local.lean (Mathlib only) — COMPILED, 0 errors, no sorry
- `N4 n = (n₀²+n₀n₂+n₂²) − 2(n₁²+n₁n₃+n₃²)`: reduced norm of `𝒪` in the coordinates of `LeafQM.ofInt`.
- `hensel_simple` (Hensel, simple root, residue form), `rep_two`, `rep_three`, `rep_ge5`,
  `rep_unit : IsUnit u → ∃ n : Fin 4 → ℤ_[p], N4 n = u` (every prime p),
  `sq_three : toZMod u = 1 → ∃ x : ℤ_[3], x² = u ∧ toZMod x = 1`.

## Step 2: Adelic.lean (Mathlib only; Local.lean included verbatim) — COMPILED, 0 errors, no sorry
- Definitions over Mathlib's `FiniteAdeleRing ℤ ℚ` (`Af`): `BR R = QuaternionAlgebra R 2 0 (-3)` (`B ⊗ R`),
  `nrdQ R : BR R →* R` (`nrdQ_eq_mul_star : ↑(nrd x) = x * star x`), `ofQ` (the kernel's `ofInt` over `R`),
  `Zhat` (adeles integral at every place), `Ohat` (ℤ̂-span of 1, i, (1+j)/2, (i+k)/2; a subring),
  `ZhatU`, `U3 = {u ∈ ℤ̂^× : u ∈ 1 + 3ℤ̂}`, `Kfull = 𝒪̂^×`, `K3 = {k ∈ 𝒪̂^× : k ∈ 1 + 3𝒪̂}`,
  `posRat` (ℚ_{>0} in 𝔸_f^×), `nrdU`, `Pi0 K = 𝔸_f^× ⧸ (ℚ_{>0} ⊔ nrd K)`.
- Proved: `nrd_Kfull_le : nrd(𝒪̂^×) ≤ ℤ̂^×`, `ZhatU_le : ℤ̂^× ≤ nrd(𝒪̂^×)`, `nrd_K3_le : nrd(K₃) ≤ U₃`,
  `U3_le : U₃ ≤ nrd(K₃)` (local representations assembled with Mathlib's `padicIntEquiv`).
- Proved: `exists_decomp : ∀ s : 𝔸_f^×, ∃ q ∈ ℚ_{>0}, s q⁻¹ ∈ ℤ̂^×`, `posQ_ZhatU : ℚ_{>0} ∩ ℤ̂^× = 1`,
  `decomp_unique`.
