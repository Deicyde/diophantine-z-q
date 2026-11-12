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

## Step 4 (11:56 PST). Acceptance-test interface (elliptic curves)
`Hodge.lean` §5. Compiles; `modelHeight_eq_faltingsHeightEC` axioms: propext, Classical.choice, Quot.sound.
- copied from scratch/pkg-I5/I5.lean: `hypGram`, `hypVol`, `finiteHeightPart`, `faltingsHeightEC`.
- `HodgeData.modelHeight_of_span`: free lattice 𝓞η₀ ⇒ h = −(2[K:ℚ])⁻¹ Σ log‖η₀‖²_σ. VERIFIED.
- `PeriodPair.lattice1` (Mathlib's period lattice in ℂ¹), `covolume_lattice1`. VERIFIED.
- `PeriodAreaFormula` (Prop, UNPROVED): covol(Λ) = hypVol 1 (4x³ − g₂x − g₃) for every PeriodPair.
- `modelHeight_eq_faltingsHeightEC`: PeriodAreaFormula + (free Néron-type lattice, periods = period
  pairs with η₀ ↦ dz, Weierstrass polynomial = 4x³−g₂x−g₃, finite part of the formula = 0)
  ⇒ modelHeight D = faltingsHeightEC W. VERIFIED (compiled).

## Step 5 (11:58 PST). Model layer signatures
File `scratch/bp-faltings/Models.lean`. `lake env lean`: no errors, no warnings.
- `AbVar`, `AbVar.baseChange` copied verbatim from ZInQKernel/HDecomp/Objects.lean.
- `genericFibre`, `GroupModel A L` (GrpObj in Over (Spec 𝓞_L), Smooth, IsSeparated,
  QuasiCompact, generic-fibre iso `gen` that is a monoid hom for the transported structure). VERIFIED.
- two sanity examples (generic fibre smooth, separated: Mathlib base-change instances). VERIFIED.

## Step 6 (12:03 PST). Rescaling; inhabited HodgeData
`Hodge.lean` §6. Compiles, no sorry.
- `HermitianLattice.rescale`, `arakelovDegree_rescale`: deg(M, c·‖·‖) = deg(M, ‖·‖) − Σ log c_σ. VERIFIED.
- `gaussianPair` (ℤ + ℤi as a PeriodPair), `ratCoeff`, `exampleHodge : HodgeData ℚ 1 ℚ`,
  `exampleHodge_modelHeight` = −½ log covol(ℤ+ℤi). VERIFIED (non-vacuity of the structure).
- instances `DiscreteTopology`, `IsZLattice ℝ` for `PeriodPair.lattice1`.

## Step 7 (12:08 PST). Fractional-ideal Hermitian lines (closed formula)
`Hodge.lean` §7. Compiles; axioms propext, Classical.choice, Quot.sound.
- `secIndex_mul_absNorm`: #(I/𝓞x)·N(I) = |N_{K/ℚ}x| for a fractional ideal I, 0 ≠ x ∈ I. VERIFIED.
- `HermitianLattice.ofFractionalIdeal`, `arakelovDegree_ofFractionalIdeal`:
  deg(I, ρ·|σ(·)|) = −log N(I) − Σ_σ log ρ_σ. VERIFIED.

## Step 8 (12:09 PST). AT1 for non-free Hodge lattices
`Hodge.lean` §8. Compiles; no `sorry` anywhere in the file (grep count 0 on the output).
- `embCoeff`, `HodgeData.ofIdeal 𝔞 L` (V = K, lattice 𝔞, periods (L σ).lattice1, ω ↦ dz).
- `HodgeData.modelHeight_ofIdeal`: h = (−log N𝔞 − ½ Σ log covol Λ_σ)/[K:ℚ]. VERIFIED.
- `modelHeight_ofIdeal_eq_faltingsHeightEC`: PeriodAreaFormula + hP (AT1b) +
  hNeron (−12 log N𝔞 = finiteHeightPart j − Σ log|σΔ|, AT1a) ⇒ h = faltingsHeightEC W. VERIFIED.

## Step 9 (12:13 PST). Base change, archimedean count
`Hodge.lean` §9. Compiles, no sorry.
- `card_embeddings_over`: #{τ : L → ℂ | τ|_K = σ} = [L:K] (via `AlgHom.card` with σ.toAlgebra). VERIFIED.
- `sum_embeddings_comp`: Σ_τ f(τ|_K) = [L:K]·Σ_σ f σ. VERIFIED.

## Step 10 (12:13 PST). AT1 for every Weierstrass model (translation)
`Hodge.lean` §10. Compiles, no sorry.
- `hypGram_comp_add`, `hypVol_one_comp_add`: hypVol 1 (P(x + c)) = hypVol 1 P. VERIFIED.
- `modelHeight_ofIdeal_eq_faltingsHeightEC'`: as §8 with P_W^σ = (4x³ − g₂x − g₃)(x + c_σ). VERIFIED.

## Step 11 (12:17 PST). Base change of the Arakelov degree (fractional-ideal lines)
`Hodge.lean` §11. Compiles; 0 errors, 0 `sorry`; axioms propext, Classical.choice, Quot.sound.
- `finrank_ringOfIntegers`: finrank (𝓞 K) (𝓞 L) = [L:K] (Mathlib `IsFractionRing.finrank_eq`). VERIFIED.
- `absNorm_map_ringOfIntegers`: N(I𝓞_L) = N(I)^[L:K] for integral ideals (Mathlib `Ideal.absNorm_algebraMap`). VERIFIED.
- `norm_algebraMap_tower`: N_{L/ℚ}(x) = N_{K/ℚ}(x)^[L:K]. VERIFIED.
- `absNorm_extendedHom`: FractionalIdeal.absNorm (extendedHom L (𝓞 L) I) = absNorm I ^ [L:K]. VERIFIED.
- `arakelovDegree_ofFractionalIdeal_baseChange`: deg_L(I𝓞_L, ρ∘res) = [L:K]·deg_K(I, ρ). VERIFIED.

## Step 12 (12:19 PST). Base-change invariance of the model height (dimension 1)
`Hodge.lean` §12. Compiles; 0 errors, 0 sorry.
- `HodgeData.modelHeight_ofIdeal_baseChange`: h_L(ofIdeal (𝔞𝓞_L) (P ∘ res)) = h_K(ofIdeal 𝔞 P). VERIFIED.

## Step 13 (12:21 PST). Normalization check covol(ℤ+ℤi) = 1
`Hodge.lean` §13. Compiles; 0 errors, 0 warnings, 0 sorry.
- `covolume_gaussianPair`: ZLattice.covolume (span ℤ {1, i}) = 1 (Lebesgue on ℂ). VERIFIED.
- `exampleHodge_modelHeight_eq_zero`. VERIFIED.
