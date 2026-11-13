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
- 11:05 Full single-file check `lake env lean scratch/infra-hodge/ProductHodgeLattice.lean` (Prefix +
  phl_1..phl_5, 7400 lines): VERIFIED exit 0 in 45 s, 0 errors, no `sorry`; all `#print axioms`
  [propext, Classical.choice, Quot.sound], incl. `productHodgeLattice_of`,
  `productMetrizationGeo_of_trivialPoints : TrivialPointsCotangent → ProductMetrizationGeo`,
  `HSyn.G0Split.heightAdditivity_of_metrization_v5` (v4 with hPL replaced by TrivialPointsCotangent).
  `verbatim_check.py`: ALL OK (ProductHodgeLattice text identical to part_prodsplit.lean and to
  infra-stalks' ProductLocalStructure.lean).
- 11:00-11:15 S-alg. FINDING: product-height's file imports the kernel (`ZInQ.DefFaltings.GroupModel` of
  ZInQKernel.HDecomp.Faltings, `PkgI3.AbVar`), metrization's file is Mathlib-only with its own copy of the
  same names, so the two Props are checked in two different single files; the generic parts phl_1-3, 4a
  compile in both (the line `--IH:ABVAR` becomes `open PkgI3 (AbVar)` in the kernel file).
  `assemble_split.py` → `SPrefix.lean` (kernel import + Mathlib + infra-stalks/ExtFrac bodies + VERBATIM
  scratch/product-height/ProductHeight.lean after its import; 12 s to olean) and `ProductSplit.lean`.
- ps_1_tools: `exists_basis_in`, `det_eq_zero_of_rows_supported`, `coeffOf`, `mkMetrized`.
- ps_2_deriv: new named Prop **`ProdUnifDeriv`** (derivative at 0 of p₁^* t along prodUnif = derivative of
  t along Φ₁ on the first block; same for p₂); `jacDet_prodUnif` (block Jacobian), `castCLE`,
  `dims_le_of_jacDet_ne_zero` (nonzero Jacobian of a (d₁, d₂)-family along prodUnif∘cast forces dᵢ ≤ gᵢ).
- ps_3_main: `metrizedZero` (dimension-0 metrized model from 0-dim uniformizations), `deltaEquiv`,
  `covolume_congr`, **`productMetrizationOfProductUnif_of : ProdUnifDeriv → ProductMetrizationOfProductUnif`**.
  g = 0: factors get dimension-0 metrizations, all heights 0 (kernel `modelHeight_dim_zero`); NO
  TrivialPointsCotangent needed here. g ≥ 1: basis of ω_P in ω_𝒢P splits; gᵢ(τ) = dᵢ by the
  dimension count; descent of jacDet Φᵢ through MP's coefficient map (no JacDetDescends needed);
  `modelHeight_add_of` gives equality of heights.
- ps_4_cor: `productModelHeight_of_splits_deriv : ProductUnifSplits → ProdUnifDeriv → ProductModelHeight`.
- 11:15 Full single-file check `lake env lean scratch/infra-hodge/ProductSplit.lean` (kernel import):
  VERIFIED exit 0 in 24 s, 0 errors, no `declaration uses sorry` (one doc-comment mention in the copied
  ProductHeight.lean header), all `#print axioms` standard. verbatim_check.py ALL OK
  (ProductMetrizationOfProductUnif identical in a25_productheight.lean and ProductHeight.lean).
- 11:19 ps_5_analytic: metrization's germ lemmas (ptC_hom_apply, one_left_apply, zero_mem_dom, evalAt_res,
  germAlong_eventuallyEq, germAlong_differentiableAt) copied to the kernel types; `prodUnif_eq`
  (prodUnif z = (Φ₁ z₁, Φ₂ z₂) ≫ e⁻¹); `ProductLocalStructureK` (metrization's statement over kernel
  types) + `productLocalStructureK` (infra-stalks' proof copied); `prodUnif_local` (metrization's
  prodPts_local adapted); **`productUnifAnalytic : ProductUnifAnalytic`** (product-height glue, as a step);
  `fderiv_germAlong_pull`; **`prodUnifDeriv : ProdUnifDeriv`**.
  ps_6_final: **`productMetrizationOfProductUnif : ProductMetrizationOfProductUnif` PROVED** (statement
  verbatim); `productModelHeight_of_unifSplits : ProductUnifSplits → ProductModelHeight`.
  Full single-file check ProductSplit.lean: VERIFIED exit 0 in 25 s, 0 errors, no sorry warning, all 14
  InfraHodge `#print axioms` (and every other axiom report in the file) [propext, Classical.choice,
  Quot.sound]. verbatim_check.py ALL OK.
- 11:25 Prefix.lean extended (after Metrization, each in its own section): VERBATIM infra-stalks
  stalk_tensor + cot_bc parts (`cotangent_baseChange_injective`) and VERBATIM infra-smooth-dim
  SmoothStalk.lean body (`InfraSmoothDim.exists_stalk_dim_of_smooth`). Prefix to olean: 48 s, 0 errors.
- phl_4c_trivial: **`trivialPointsCotangent : TrivialPointsCotangent` PROVED**. Proof: X = 𝒢 ×_{𝓞_L} Spec ℂ
  (via τ) is smooth, LFT over ℂ, Jacobson (`LocallyOfFiniteType.jacobsonSpace`); closed points are
  ℂ-points (Mathlib `pointOfClosedPoint`, `pointEquivClosedPoint`), a ℂ-point over Spec ℂ is a τ-point of
  𝒢, all equal to 1, so X has one closed point z₀, hence one point (`closure_inter_closedPoints`);
  `ringKrullDim_stalk_eq_coheight` ⇒ dim 𝒪_{z₀} = 0; `exists_stalk_dim_of_smooth` ⇒ spanFinrank 𝔪 = 0 ⇒
  𝔪 = ⊥; `cotangent_baseChange_injective` + `Module.Flat.linearIndependent_one_tmul` ⇒ ω_{A_L} = 0.
  Pitfall: `pullback f g` in binder/Set positions elaborated in `Type` (write `(pullback f g : Scheme)`);
  `IsLocalRing` of `(Spec ↧ℂ).presheaf.stalk (closedPoint ℂ)` not found by instance search (use a
  helper lemma with `x : X` typed).
- phl_5_cor: **`productHodgeLattice : ProductHodgeLattice` PROVED** (statement verbatim);
  `ZInQ.Metrization.productMetrizationGeo_infraHodge : ProductMetrizationGeo`;
  `HSyn.G0Split.heightAdditivity_of_metrization_v5` (v4 without hPL).
- 11:29 Full single-file check ProductHodgeLattice.lean: VERIFIED exit 0 in 52 s, 0 errors, no sorry
  warning, all axiom reports standard (11 InfraHodge/consequence prints). verbatim_check.py ALL OK
  (output in verbatim_check_out.txt).
