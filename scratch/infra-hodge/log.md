# infra-hodge results log

- 10:30 Merged origin/wip/infra-stalks (e440e8da) and origin/wip/hodge-bc2 (4417ccb9).
- Layout: `assemble.py` builds `Prefix.lean` = import Mathlib + VERBATIM infra-stalks StalkPullback /
  CotangentProduct bodies, cot_pullback + local_structure parts, VERBATIM hodge-bc2
  `ZInQKernel/Contrib/HodgeBC2/ExtFrac.lean` body, VERBATIM `scratch/metrization/Metrization.lean`
  (owner text of `ProductHodgeLattice`), VERBATIM infra-stalks pls_proof part. Prefix compiled to
  /tmp olean (3 min 23 s wall, 0 errors) for the dev loop (tail ~25 s).
- phl_1_cot (VERIFIED compiles): `cotMapAt f h` (cotangent map between named points), `_comp`, `_id`,
  `_congr`, `_smul`, `cotMapAt_comp_eq_zero` (through a point with field stalk); hodge-bc2's `φL`,
  `cotL`, `cotL_isScalarTower` (copied); `cotG_smul_ring`, `cotG_smulL` (cotangent maps of morphisms
  over 𝓞_L are 𝓞_L- and L-linear), `cotGL`.
- phl_2_split (VERIFIED): `cotG_omegaAt`/`cotG_omega` (a morphism of group models with η ≫ φ = η maps
  ω_s into ω_s; no conormal-of-product computation needed); `incl1/incl2` (i₁ = (id,1) ≫ e⁻¹);
  `cot_i1_p1`, `cot_i2_p2`, `cot_i1_p2 = 0`, `cot_i2_p1 = 0`; **`cot_split`**:
  v = p₁^*(i₁^* v) + p₂^*(i₂^* v) (infra-stalks `sub_mem_sq_pairPt` transported along e).
- phl_3_linalg (VERIFIED): `detIdeal`, `det_prod_block`, **`detIdeal_prod`**
  (detIdeal (u.prod w) (W₁×W₂) = detIdeal u W₁ * detIdeal w W₂, multilinear expansion + column sort),
  `idx`, `idx_mul_absNorm`, **`idx_mul`** ([I₁I₂:𝓞] = [I₁:𝓞][I₂:𝓞] for 1 ∈ I₁, I₂), `delta`
  (L ⊗ ⋀^n V → L via extFracEquiv), `finrank_hodge`, `delta_injective`, `relIndex_detLat`.
- phl_4_main (VERIFIED, 11:40): `basis_of_wedge_ne_zero`, `exists_omega_basis`, new named Prop
  `TrivialPointsCotangent` (used only when g₁ = 0 or g₂ = 0), `subsingleton_of_dim_zero`,
  **`productHodgeLattice_of : TrivialPointsCotangent → ProductHodgeLattice`**;
  `#print axioms` = [propext, Classical.choice, Quot.sound] (dev loop against the olean prefix).
  FINDING: for g₁ = 0 the Prop needs ω_{A_L} = 0 for the factor, which MetrizedModel only forces
  through `arch` (Φ : ℂ⁰ → 𝒢(ℂ)_τ surjective, so 𝒢(ℂ)_τ is trivial); hence the named Prop.
