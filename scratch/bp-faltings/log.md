# bp-faltings results log

## Step 1 (11:47 PST). Hermitian line bundles on Spec 𝓞_K, Arakelov degree
File `scratch/bp-faltings/Hodge.lean` §§1-2. `lake env lean`: no errors, no warnings.
- `sum_log_norm_embeddings`: ∑_{σ:K→ℂ} log‖σx‖ = log|N_{K/ℚ}x| (x ≠ 0). VERIFIED (compiled).
- `secIndex_smul`: #(M/𝓞·as) = |N a|·#(M/𝓞·s) for a ∈ 𝓞_K, 0 ≠ s ∈ M. VERIFIED.
- `HermitianLattice` (rank-one lattice in a K-line + norms at each σ), `degreeAt`,
  `secIndex_ne_zero` (one nonzero section of finite index ⇒ all), `degreeAt_eq`,
  `arakelovDegree`, `degreeAt_eq_arakelovDegree` (independence of the section). VERIFIED.
