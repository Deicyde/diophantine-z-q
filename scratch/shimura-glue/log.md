# shimura-glue results log

## Setup
- `.lake/build`, `lean/.lake/build` reflink-copied from ~/dzq-check2 (commit 5da857b0; only
  `ZInQKernel/OneProof/TYZSplit.lean` differs from this base, docstring only).

## Step 1: Local.lean (Mathlib only) — COMPILED, 0 errors, no sorry
- `N4 n = (n₀²+n₀n₂+n₂²) − 2(n₁²+n₁n₃+n₃²)`: reduced norm of `𝒪` in the coordinates of `LeafQM.ofInt`.
- `hensel_simple` (Hensel, simple root, residue form), `rep_two`, `rep_three`, `rep_ge5`,
  `rep_unit : IsUnit u → ∃ n : Fin 4 → ℤ_[p], N4 n = u` (every prime p),
  `sq_three : toZMod u = 1 → ∃ x : ℤ_[3], x² = u ∧ toZMod x = 1`.
