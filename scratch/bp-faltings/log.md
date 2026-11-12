# bp-faltings results log

## Step 1 (11:47 PST). Hermitian line bundles on Spec 𝓞_K, Arakelov degree
File `scratch/bp-faltings/Hodge.lean` §§1-2. `lake env lean`: no errors, no warnings.
- `sum_log_norm_embeddings`: ∑_{σ:K→ℂ} log‖σx‖ = log|N_{K/ℚ}x| (x ≠ 0). VERIFIED (compiled).
- `secIndex_smul`: #(M/𝓞·as) = |N a|·#(M/𝓞·s) for a ∈ 𝓞_K, 0 ≠ s ∈ M. VERIFIED.
- `HermitianLattice` (rank-one lattice in a K-line + norms at each σ), `degreeAt`,
  `secIndex_ne_zero` (one nonzero section of finite index ⇒ all), `degreeAt_eq`,
  `arakelovDegree`, `degreeAt_eq_arakelovDegree` (independence of the section). VERIFIED.

## Step 2 (11:51 PST). Archimedean term on a complex torus
`Hodge.lean` §3. Compiles, no warnings.
- `covolume_comap_mul_det`: covol(e⁻¹Λ)·|det e| = covol Λ for e : E ≃L[ℝ] E, any Haar μ. VERIFIED.
- `det_restrictScalars_complex`: det_ℝ T = normSq(det_ℂ T). VERIFIED (from Mathlib's
  `LinearMap.det_restrictScalars`).
- `torusMetricSq Λ c = ‖c‖²·covol Λ`; `torusMetricSq_eq_setIntegral` (= ∫_F |c|² over any
  fundamental domain F); `torus_setIntegral_indep` (periodic densities); `torusMetricSq_pos`;
  `torusMetricSq_comap` (coordinate change z = Tz': Λ ↦ T⁻¹Λ, c ↦ c·det T, metric unchanged). VERIFIED.

## Step 3 (11:53 PST). Metrized Hodge bundle and model height
`Hodge.lean` §4. Compiles; axioms of all main theorems: propext, Classical.choice, Quot.sound.
- `HodgeData K g V` (lattice ∧^gω_𝒢 in the K-line V, period lattices Λ_σ ⊂ ℂ^g, σ-semilinear
  coefficient maps V → ℂ); `norm`, `norm_sq` (= torusMetricSq), `hodgeBundle : HermitianLattice`.
- `modelHeight := deg(ω̄)/[K:ℚ]`; `modelHeight_eq`: Faltings' formula for every nonzero η. VERIFIED.
- `recoord`, `modelHeight_recoord`: independent of linear coordinates at every σ. VERIFIED.
- `modelHeight_eq_add_of_le`: ω' ≤ ω ⇒ h(ω) = h(ω') + log[ω:ω']/[K:ℚ]; `modelHeight_le_of_le`. VERIFIED.
