# metrization results log

Start 2026-11-13 04:08 PST. Base 2dd83306 (wip/integrate-w36b). Targets (verbatim from
scratch/g0-heightadd/part_heightadd.lean, part_prod.lean): `ZInQ.G0HeightAdd.MetrizationDimUnique`,
`MetrizationExists`, `ProductMetrizationGeo`.

## Run 1: ExtLine.lean (Mathlib only) — COMPILED 04:15 (3 min 10 s wall, load 28; 0 errors)
- `ZInQ.Metrization.eq_of_finrank_one`: for `R` comm ring, `F` a field, flat `R`-algebra, any
  `R`-module `C`, `0 < g`, `0 < g'`, `finrank F (F ⊗_R ⋀^g C) = 1`, `finrank F (F ⊗_R ⋀^{g'} C) = 1`
  ⇒ `g = g'`. Axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
  Proof: for `g < g + n`, pick `v` with `1 ⊗ ιMulti v ≠ 0` in `F ⊗ ⋀^{g+n}`, split `v = append a b`,
  swap one entry between `a` and `b`; right multiplication by `ιMulti b`, `ιMulti b'` separates
  `1 ⊗ ιMulti a` and `1 ⊗ ιMulti a'`, contradicting `finrank = 1` (flatness keeps
  `1 ⊗ ιMulti v ≠ 0` in `F ⊗ ⋀C`).

## Run 2: Metrization.lean (build.sh: Base.lean + ExtLine + part_dim) — FAILED (dot-notation
  on `ZInQ.Metrization.MetrizedModel.*` names; renamed to `metrized_*`).

## Run 3: Metrization.lean = Base.lean + ExtLine body + part_dim + part_g0dim + part_exists —
COMPILED 04:23 (41 s; 0 errors). `Base.lean` is byte-identical to scratch/g0-heightadd/HeightAdd.lean
(`cmp`), so the three target Props are the verbatim originals. VERIFIED.
- `ZInQ.Metrization.metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique` — PROVED, no
  hypotheses. Axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
  (g, g' ≥ 1: `eq_of_finrank_one` on `hodgeSpace = L ⊗_{𝓞_L} ⋀^g cotangent`, `L` flat over `𝓞_L`
  by `IsLocalization.flat`; g = 0 < g': `Φ : ℂ⁰ → 𝒢(ℂ)_τ` onto makes the points subsingleton,
  while a discrete kernel in `ℂ^{g'}` (ℝ connected) gives `Φ z ≠ 1`.)
- `part_g0dim.lean` = scratch/g0-dim/part_dim.lean l. 1-208 verbatim (namespace `G0Dim`) + `end`.
- `abVar_dim_finite` (def-faltings' `AbVar` has `dim ∈ ℕ`): PROVED from `G0Dim.dim_finite`. VERIFIED.
- new Props: `AnalyticUniformizationOfDim` (leaf: uniformization theorem at g = dim A),
  `JacDetDescends` (glue), `JacDetNondegenerate` (glue).
- `analyticUniformizationExists_of : AnalyticUniformizationOfDim → AnalyticUniformizationExists`,
  `exists_metrization_of_dim`, `metrizationExists_of : HodgeLatticeTheorem →
  AnalyticUniformizationOfDim → JacDetDescends → JacDetNondegenerate → MetrizationExists`,
  `metrized_dim_eq` (every metrization has g = dim A, same hypotheses): all compiled,
  axioms [propext, Classical.choice, Quot.sound]. VERIFIED.

## Run 4: + part_prodgeo — COMPILED 04:27 (2 min 8 s; 0 errors)
- new: `leftBlock`, `rightBlock`, `prodLattice`, `prodPts`; Props `ProductLatticeFacts` (pure
  Mathlib glue), `ProductUniformization` (glue), `ProductHodgeCompat` (glue).
- `productMetrizationGeo_of : JacDetDescends → ProductUniformization → ProductLatticeFacts →
  ProductHodgeCompat → ProductMetrizationGeo`: axioms [propext, Classical.choice, Quot.sound]. VERIFIED.

## Run 5-6: ProdLattice.lean (Mathlib only) — first attempt 3 errors (Subtype.val unification,
  membership in `prodLattice`, beta-redex before `rw [Submodule.vadd_def]`); fixed —
  COMPILED 04:32 (7 s; 0 errors).
- `productLatticeFacts : ProductLatticeFacts` PROVED (discreteness by injecting into `Λ₁ × Λ₂`;
  full rank via `Fin.append x 0 + Fin.append 0 y`; covolume: fundamental domain
  `φ⁻¹(F₁ ×ˢ F₂)`, `φ = blockLinearEquiv` volume-preserving (piCongrLeft ∘ sumPiEquivProdPi),
  `Measure.prod_prod`). Axioms [propext, Classical.choice, Quot.sound]. VERIFIED.

## Run 7: Metrization.lean with part_prodlat + part_final — COMPILED 04:34 (30 s; 0 errors)
- `productMetrizationGeo_of' : JacDetDescends → ProductUniformization → ProductHodgeCompat →
  ProductMetrizationGeo`; `HSyn.G0Split.heightAdditivity_of_metrization : N1 → LeafAdopt.H5 →
  AnalyticUniformizationUnique → HodgeLatticeTheorem → AnalyticUniformizationOfDim →
  JacDetDescends → JacDetNondegenerate → ProductUniformization → ProductHodgeCompat →
  HeightAdditivity`. All #print axioms [propext, Classical.choice, Quot.sound]. VERIFIED.

## Run 8: + part_produnif — COMPILED 04:37 (1 min 40 s; 0 errors)
- `prodPts_alg`: for `e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G` with `IsMonHom (e.hom ≫ fst)`, `IsMonHom (e.hom ≫ snd)`
  and analytic uniformizations `Φᵢ`: `prodPts e Φ₁ Φ₂` is a homomorphism, has kernel exactly
  `prodLattice Λ₁ Λ₂`, and is surjective. PROVED (MonObj.mul_comp, one_comp, hom_ext). VERIFIED.
- new glue `ProductUniformizationAnalytic` (open `dom`, holomorphy only);
  `productUniformization_of : ProductUniformizationAnalytic → ProductUniformization`;
  `HSyn.G0Split.heightAdditivity_of_metrization'` (with `ProductUniformizationAnalytic` in place
  of `ProductUniformization`). Axioms [propext, Classical.choice, Quot.sound]. VERIFIED.

## Run 9-10: + part_jacdet — first attempt 6 errors (DecidableEq instance mismatch in
  `Function.update` under `rw`, ambiguous `mul_assoc`/`one_mul` with `open MonObj`); fixed with
  `convert` and `_root_.` — COMPILED 04:42 (28 s; 0 errors)
- new glue `JacDetMultilinear` (four calculus properties of `jacDet`: class invariance,
  slot additivity, `τ(a)`-scaling, vanishing on equal slots).
- `jacDetDescends_of : JacDetMultilinear → JacDetDescends` PROVED (alternating map through
  `Function.surjInv` of `toCotangent`, `exteriorPower.alternatingMapLinearEquiv`, `TensorProduct.lift`
  of `(x, w) ↦ τ x · Ψ w`, semilinearity by tensor induction). VERIFIED.
- `HSyn.G0Split.heightAdditivity_of_metrization'' : N1 → LeafAdopt.H5 → AnalyticUniformizationUnique →
  HodgeLatticeTheorem → AnalyticUniformizationOfDim → JacDetMultilinear → JacDetNondegenerate →
  ProductUniformizationAnalytic → ProductHodgeCompat → HeightAdditivity`. Axioms
  [propext, Classical.choice, Quot.sound]. VERIFIED.

## Run 11-12: + part_prodsplit — first attempt 1 error (`IsMonHom.one_hom` needs explicit `φ`);
  fixed — COMPILED 04:48 (54 s; 0 errors)
- `map_genericUnit_of_isMonHom`: a homomorphism of group models maps `ξ` to `ξ` (from
  `IsMonHom.one_hom`). PROVED. New def `pullGerm φ : 𝒪_{ℋ,ξ} ⟶ 𝒪_{𝒢,ξ}` (stalkSpecializes ≫ stalkMap).
- new glue `ProductHodgeLattice` (algebra) and `ProductJacobian` (analysis, block-diagonal Jacobian).
- `productHodgeCompat_of : ProductUniformization → ProductHodgeLattice → ProductJacobian →
  ProductHodgeCompat` PROVED; `HSyn.G0Split.heightAdditivity_of_metrization''' : N1 → H5 → U →
  HodgeLatticeTheorem → AnalyticUniformizationOfDim → JacDetMultilinear → JacDetNondegenerate →
  ProductUniformizationAnalytic → ProductHodgeLattice → ProductJacobian → HeightAdditivity`.
  Axioms [propext, Classical.choice, Quot.sound]. VERIFIED.

## Run 13-15: + part_jacgerm — attempts 1-2: errors (prime instance on a Spec point, `mul_one`
  ambiguity, `1`-instance mismatch needing `erw`, `map_add` across `Γ(ptC.left, ⊤)` vs
  `Γ(Spec ℂ, ⊤)`, `Opens` inf membership); fixed — COMPILED 04:57 (31 s; 0 errors)
- PROVED: `ptC_hom_apply` (`Spec ℂ → Spec 𝓞_L` via `τ` hits the generic point), `one_left_apply`
  (the identity point lies over `ξ`), `zero_mem_dom` (`0 ∈ dom Φ U` if `ξ ∈ U`), `evalAt_res`,
  `evalAt_add`, `germAlong_eventuallyEq` (`germAlong Φ t` agrees near `0` with any representative),
  `germAlong_differentiableAt`, `germAlong_add_eventuallyEq`, `jacDet_update_add` (clause (ii)),
  `jacDet_eq_zero_of_eq` (clause (iv)).
- new glue `JacDetClassScalar` (clauses (i), (iii)); `jacDetMultilinear_of : JacDetClassScalar →
  JacDetMultilinear` PROVED. Axioms [propext, Classical.choice, Quot.sound]. VERIFIED.

## Run 16-17: + part_jacscalar — attempt 1: 1 error (final `ΓSpecIso_naturality` step needed
  `ConcreteCategory.comp_apply`); fixed — COMPILED 05:01 (34 s; 0 errors)
- PROVED: `evalAt_mul`, `evalAt_structSection` (the image of `a ∈ 𝓞_L` evaluates to `τ(a)` at
  every complex point; `Over.w`, `appLE_eq_app`, `comp_appTop`, `ΓSpecIso_naturality`),
  `germAlong_structMap_mul_eventuallyEq`, `jacDet_update_smul` (clause (iii)).
- new glue `JacDetClassInvariant` (clause (i) only); `jacDetClassScalar_of :
  JacDetClassInvariant → JacDetClassScalar` PROVED. Axioms [propext, Classical.choice,
  Quot.sound]. VERIFIED.

## Run 18-21: + part_jacclass — attempts 1-3: errors (presheaf of `ptC.left` vs `Spec ℂ` not
  syntactically equal: worked through `q' : Spec ℂ ⟶ 𝒢.G.left := q` and `change`; instances on
  `(Over.mk _).left` stalks; `Ideal.toCotangent_eq` takes `I` explicitly; `x ∈ ⊤` not `trivial`;
  product rule via `fderiv_mul` + `ext; simp`) — COMPILED 05:08 (33 s; 0 errors)
- PROVED: `evalAt_one_eq_zero` (a section with germ in `𝔪_ξ` vanishes at the identity complex point:
  `germ_stalkMap`, local `stalkMap`, stalk of `Spec ℂ` at its generic point is a field,
  `germ_injective_of_isIntegral`), `germAlong_zero_of_mem`, `germAlong_mul_eventuallyEq`,
  `fderiv_germAlong_eq_zero_of_mem_sq` (induction on `𝔪 * 𝔪`), `jacDet_congr_dCls` (clause (i)),
  `jacDetClassInvariant`.
- **`ZInQ.Metrization.jacDetDescends : JacDetDescends` PROVED, no hypotheses.** VERIFIED.
- `metrizationExists_of' : HodgeLatticeTheorem → AnalyticUniformizationOfDim → JacDetNondegenerate →
  MetrizationExists`; `productMetrizationGeo_of'' : ProductUniformizationAnalytic →
  ProductHodgeLattice → ProductJacobian → ProductMetrizationGeo`;
  `HSyn.G0Split.heightAdditivity_of_metrization_final : N1 → H5 → U → HodgeLatticeTheorem →
  AnalyticUniformizationOfDim → JacDetNondegenerate → ProductUniformizationAnalytic →
  ProductHodgeLattice → ProductJacobian → HeightAdditivity`. All axioms [propext, Classical.choice,
  Quot.sound]; `grep -c sorry Metrization.lean` = 0. VERIFIED.

## Run 22-23: + part_prodjac — attempt 1: errors (`change` across `ptC.left`/`Spec ℂ`, a bad
  `Function.comp_apply.symm`, a malformed helper); fixed — COMPILED 05:11 (32 s; 0 errors)
- PROVED: `pullGerm_germ`, `evalAt_comp` (evaluation along a morphism of models; `comp_appLE`),
  `germAlong_pull_fst_eventuallyEq`, `germAlong_pull_snd_eventuallyEq`
  (`(p₁*t) ∘ prodPts = (t ∘ Φ₁) ∘ leftBlock` near `0`), `fderiv_comp_linear`, and
  **`productJacobian : ProductJacobian`** (block-diagonal Jacobian; `reindex finSumFinEquiv`,
  `det_fromBlocks_zero₂₁`).
- `productMetrizationGeo_of''' : ProductUniformizationAnalytic → ProductHodgeLattice →
  ProductMetrizationGeo`; `HSyn.G0Split.heightAdditivity_of_metrization_v2 : N1 → H5 → U →
  HodgeLatticeTheorem → AnalyticUniformizationOfDim → JacDetNondegenerate →
  ProductUniformizationAnalytic → ProductHodgeLattice → HeightAdditivity`. Axioms
  [propext, Classical.choice, Quot.sound]. VERIFIED.

## Run 24: + part_produnif2 — COMPILED 05:16 (1 min 26 s; 0 errors)
- new glue `ProductLocalStructure` (pure algebraic geometry at complex points: near `(p₁, p₂)`,
  membership in `U` and a section of `U` are given by sums of products of regular functions on
  `V₁ ⊂ 𝒢₁`, `V₂ ⊂ 𝒢₂`).
- `prodPts_local`, `productUniformizationAnalytic_of : ProductLocalStructure →
  ProductUniformizationAnalytic` PROVED (open neighbourhoods `O ∩ H⁻¹{0}ᶜ`, quotient of
  holomorphic functions). `productMetrizationGeo_of_local : ProductLocalStructure →
  ProductHodgeLattice → ProductMetrizationGeo`; `HSyn.G0Split.heightAdditivity_of_metrization_v3 :
  N1 → H5 → U → HodgeLatticeTheorem → AnalyticUniformizationOfDim → JacDetNondegenerate →
  ProductLocalStructure → ProductHodgeLattice → HeightAdditivity`. Axioms [propext,
  Classical.choice, Quot.sound]. VERIFIED.
