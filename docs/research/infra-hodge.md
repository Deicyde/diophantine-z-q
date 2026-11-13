# infra-hodge: the two product Props left by infra-stalks are proved

Task infra-hodge, 2026-11-13. Lean: `scratch/infra-hodge/` (results log `scratch/infra-hodge/log.md`).
Base: fork main 57a7fa26 + merges of `origin/wip/infra-stalks` (e440e8da) and `origin/wip/hodge-bc2`
(4417ccb9). No existing file of the project was edited; every other task's Lean is copied verbatim
into the assembled files by `assemble.py` / `assemble_split.py`, and `verbatim_check.py` checks this
mechanically. This is model work; no human has reviewed it.

Marks: **VERIFIED** = compiled here with `lake env lean` (0 errors, no `sorry`) or read in a source.
**STANDARD** = published. **UNVERIFIED** = locator from memory (no network).

## 0. Main result

**Both target Props are theorems, with their owners' statements verbatim and no hypotheses
(VERIFIED):**

| Prop (owner) | theorem | single-file check |
|---|---|---|
| `ZInQ.Metrization.ProductHodgeLattice` (metrization; also in infra-stalks' `ProductLocalStructure.lean`) | `ZInQ.InfraHodge.productHodgeLattice : ZInQ.Metrization.ProductHodgeLattice` | `scratch/infra-hodge/ProductHodgeLattice.lean`, exit 0, 52 s |
| `ZInQ.ProductHeight.ProductMetrizationOfProductUnif` (product-height S-alg; field `productMetrizationOfProductUnif` of g0-assemble2's `GluePieces3`) | `ZInQ.InfraHodge.productMetrizationOfProductUnif : ZInQ.ProductHeight.ProductMetrizationOfProductUnif` | `scratch/infra-hodge/ProductSplit.lean`, exit 0, 25 s |

`#print axioms` output (both files; every other axiom report in the two files is the same):

```
'ZInQ.InfraHodge.productHodgeLattice' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.InfraHodge.productMetrizationOfProductUnif' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Three further glue Props were proved on the way (all VERIFIED, standard axioms):
- `ZInQ.InfraHodge.trivialPointsCotangent : TrivialPointsCotangent` (new named Prop, introduced
  and discharged here: a smooth group model whose complex points at some `τ` are trivial has zero
  cotangent space; this is what `ProductHodgeLattice` needs when a factor has `g = 0`);
- `ZInQ.InfraHodge.prodUnifDeriv : ProdUnifDeriv` (new named Prop, introduced and discharged here:
  derivative at `0` of a pulled-back germ along `prodUnif`);
- **`ZInQ.InfraHodge.productUnifAnalytic : ZInQ.ProductHeight.ProductUnifAnalytic`**: product-height's
  glue "analytic half of the product uniformization", statement verbatim (it is in the same verbatim
  copy of `ProductHeight.lean`).

Consequences (VERIFIED, same files):
- `ZInQ.Metrization.productMetrizationGeo_infraHodge : ZInQ.G0HeightAdd.ProductMetrizationGeo`
  (g0-heightadd's P2a-geo, in metrization's copy), via infra-stalks' `productMetrizationGeo_of_hodgeLattice`;
- `HSyn.G0Split.heightAdditivity_of_metrization_v5 (hN1) (h5) (hU) (hH) (hUD) (hN) : HeightAdditivity`
  (infra-stalks' `_v4` without `hPL : ProductHodgeLattice`);
- `ZInQ.InfraHodge.productModelHeight_of_unifSplits (hS : ProductUnifSplits) : ZInQ.H5Neron.ProductModelHeight`:
  product-height's route S for P2 now rests on the single analytic glue Prop S-an (`ProductUnifSplits`).

No statement change is proposed.

## 1. The statements proved (verbatim)

`ProductHodgeLattice` (scratch/metrization/part_prodsplit.lean): for `e : 𝒢P ≅ M₁.model ⊗ M₂.model`
with homomorphic projections, `finrank L (𝒢P.hodgeSpace (g₁ + g₂)) = 1`, and there are germs
`f₁, f₂`, `f = (p₁^* f₁, p₂^* f₂)` and `a₁, a₂ ∈ L` with `aᵢ • wedge fᵢ` nonzero in `Mᵢ.hodge.lattice`,
`(a₁a₂) • wedge f` nonzero in `𝒢P.detLattice (g₁+g₂)`, and
`secIndex (𝒢P.detLattice (g₁+g₂)) ((a₁a₂) • wedge f) = secIndex M₁.hodge.lattice (a₁ • wedge f₁) *
secIndex M₂.hodge.lattice (a₂ • wedge f₂)`. (Full text: `verbatim_check.py` compares it with the owner
file.) The proof takes `a₁ = a₂ = 1`.

`ProductMetrizationOfProductUnif` (scratch/g0-assemble2/parts/a25_productheight.lean, identical text in
scratch/product-height/ProductHeight.lean): if at every `τ` the metrization `MP` of `𝒢P ≅ 𝒢₁ ⊗ 𝒢₂`
has period lattice `Λ₁ × Λ₂` and coefficient map computed by `prodUnif e Φ₁ Φ₂` (dimensions
`g₁(τ) + g₂(τ) = g`), then there are metrizations `M₁` of `𝒢₁`, `M₂` of `𝒢₂` with
`h(M₁) + h(M₂) ≤ h(MP)`. The proof gives equality.

The two named Props introduced (both proved):

```lean
def TrivialPointsCotangent : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L) (τ : L →+* ℂ), (∀ p : 𝒢.Pts τ, p = 1) → Subsingleton 𝒢.cotangent

def ProdUnifDeriv : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L) (𝒢₂ : GroupModel B L)
    (e : 𝒢P.G ≅ 𝒢₁.G ⊗ 𝒢₂.G) [IsMonHom (e.hom ≫ fst _ _)] [IsMonHom (e.hom ≫ snd _ _)]
    (τ : L →+* ℂ) (g₁ g₂ : ℕ) (Λ₁ : Submodule ℤ (Fin g₁ → ℂ)) (Λ₂ : Submodule ℤ (Fin g₂ → ℂ))
    (Φ₁ : (Fin g₁ → ℂ) → 𝒢₁.Pts τ) (Φ₂ : (Fin g₂ → ℂ) → 𝒢₂.Pts τ),
    𝒢₁.IsAnalyticUniformization τ Λ₁ Φ₁ → 𝒢₂.IsAnalyticUniformization τ Λ₂ Φ₂ →
    (∀ (t : 𝒢₁.genStalk) (v : Fin (g₁ + g₂) → ℂ),
      fderiv ℂ (𝒢P.germAlong (prodUnif e Φ₁ Φ₂)
          (((e.hom ≫ fst _ _).left.stalkMapAt (hp1 e)).hom t)) 0 v =
        fderiv ℂ (𝒢₁.germAlong Φ₁ t) 0 (fun i => v (Fin.castAdd g₂ i))) ∧
    (∀ (t : 𝒢₂.genStalk) (v : Fin (g₁ + g₂) → ℂ),
      fderiv ℂ (𝒢P.germAlong (prodUnif e Φ₁ Φ₂)
          (((e.hom ≫ snd _ _).left.stalkMapAt (hp2 e)).hom t)) 0 v =
        fderiv ℂ (𝒢₂.germAlong Φ₂ t) 0 (fun j => v (Fin.natAdd g₁ j)))
```

## 2. How the proofs go

**Cotangent maps and the splitting (parts `phl_1_cot`, `phl_2_split`).**
- `cotMapAt f h : 𝔪_y/𝔪_y² → 𝔪_x/𝔪_x²` for a morphism of schemes with `f x = y` (via infra-stalks'
  `stalkMapAt`), functorial, and zero when it factors through a point whose local ring is a field.
- For morphisms of group models over `𝓞_L` it is `𝓞_L`-linear and `L`-linear for hodge-bc2's
  `L`-structure `cotL` (copied).
- `cotG_omega`: a morphism `φ` with `η ≫ φ = η` maps `ω_ℋ` into `ω_𝒢`. It maps generators of
  `omegaAt s` to generators, using naturality of specialization maps. So no computation of the
  conormal sheaf of a product at closed points is needed.
- With `i₁ = (id, 1) ≫ e⁻¹` and `i₂ = (1, id) ≫ e⁻¹`: `i₁^*p₁^* = id`, `i₁^*p₂^* = 0` (the map
  factors through the generic point of `Spec 𝓞_L`), and
  **`cot_split`: `v = p₁^*(i₁^* v) + p₂^*(i₂^* v)`**. The last is infra-stalks'
  `sub_mem_sq_pairPt`, transported along `e`.
- Hence `Ψ = (p₁^*, p₂^*) : ω₁ × ω₂ ≅ ω_P` as `L`-spaces, and `v ∈ ω_𝒢P ↔ i₁^* v ∈ ω₁ ∧ i₂^* v ∈ ω₂`.

**Determinant ideals and indices (part `phl_3_linalg`, pure algebra).**
- `detIdeal b W = span_{𝓞} {b.det v | v ∈ W^n} ⊆ L`.
- **`detIdeal_prod`**: `detIdeal (u.prod w) (W₁ × W₂) = detIdeal u W₁ * detIdeal w W₂`. Expand
  `det(a + b)` multilinearly (`MultilinearMap.map_add_univ`). A term is `0` unless exactly `g₁`
  columns come from `W₁`, by linear independence and finrank. Otherwise a column permutation gives a
  block-diagonal matrix (`Matrix.det_fromBlocks_zero₂₁`).
- **`idx_mul`**: `[I₁I₂ : 𝓞] = [I₁ : 𝓞][I₂ : 𝓞]` for `𝓞`-submodules of `L` containing `1`. If both
  indices are finite, `n·Iᵢ ⊆ 𝓞` (`nsmul_mem_of_relIndex_ne_zero_of_dvd` with `n = idx!`) gives
  integral ideals `Jᵢ` with `𝓞Jᵢ = nᵢIᵢ`. Then `idx(I) · N(J) = N(n)` (`idx_mul_absNorm`), and
  `Ideal.absNorm` is multiplicative. Infinite indices are handled by a tower argument.
- `delta b : L ⊗_𝓞 ⋀^n_𝓞 V → L`, `1 ⊗ ιMulti v ↦ b.det v`, built through hodge-bc2's
  `extFracEquiv`. It is injective because the Hodge line has finrank `1`
  (`exteriorPower.finrank_eq`). So `secIndex (⋀^n W) (1 ⊗ ιMulti b) = idx (detIdeal b W)`
  (`relIndex_detLat`).

**`ProductHodgeLattice` (parts `phl_4a_basis`, `phl_4b_main`, `phl_4c_trivial`).**
- `exists_omega_basis`: a metrized model of dimension `g ≥ 1` has an `L`-basis of `ω_{A_L}` inside
  `ω_𝒢`. Some generator `1 ⊗ ιMulti v` of the lattice is nonzero (`isLattice`), so `v` is
  independent. A vector outside its span would give `g + 1` independent wedges in a line
  (`ιMulti_family_linearIndependent_field`).
- For `g = 0`, `arch` makes `𝒢(ℂ)_τ` trivial, and `trivialPointsCotangent` gives `ω = 0`:
  - `X = 𝒢 ×_{𝓞_L} Spec ℂ` is smooth and of finite type, hence Jacobson;
  - its closed points are `ℂ`-points (Mathlib's `pointEquivClosedPoint`), which are `τ`-points of
    `𝒢`, all equal to `1`, so `X` is a single point;
  - `dim 𝒪_{X,z₀} = 0` (`ringKrullDim_stalk_eq_coheight`), so infra-smooth-dim's
    `exists_stalk_dim_of_smooth` gives `𝔪_{z₀} = 0`;
  - infra-stalks' `cotangent_baseChange_injective` gives `ℂ ⊗ ω_{A_L} ↪ 0`.
- Take bases `u ⊆ ω₁`, `w ⊆ ω₂`, `B = Ψ(u ⊔ w)`, germs `fᵢ` with `dfᵢ = uᵢ`, `wᵢ`, and
  `f = (p₁^* f₁, p₂^* f₂)` (so `df = B`), with `a₁ = a₂ = 1`. Then:
  - `finrank = 1` (`finrank_hodge B`);
  - memberships hold (`B ⊆ ω_P` by `cotG_omega`);
  - `secIndex = idx(detIdeal B ω_P) = idx(detIdeal u ω₁ · detIdeal w ω₂) = product`.

**`ProductMetrizationOfProductUnif` (parts `ps_1`–`ps_6`, kernel types).**
- `g = 0`: both factors get metrizations of dimension `0` from the given `0`-dimensional
  uniformizations (`metrizedZero`, through `mkMetrized`). All heights are `0` (kernel
  `modelHeight_dim_zero`).
- `g ≥ 1`, the dimensions and bases:
  - a basis of `ω_{A_L}` of `MP` inside `ω_{𝒢P}` splits through `Ψ`, so `dim ωᵢ = dᵢ`,
    `d₁ + d₂ = g`, with bases `u ⊆ ω₁`, `w ⊆ ω₂` (`exists_basis_in`);
  - `jacDet_prodUnif`: from `ProdUnifDeriv`, the Jacobian of `(p₁^* f, p₂^* h)` along `prodUnif` is
    `jacDet Φ₁ f · jacDet Φ₂ h`;
  - `dims_le_of_jacDet_ne_zero`: a family with `d₁` germs from `𝒢₁` and `d₂` from `𝒢₂` has rows
    supported on `g₁(τ)`, resp. `g₂(τ)`, columns (`det_eq_zero_of_rows_supported`). Since
    `coeff_τ(wedge F) ≠ 0`, this forces `gᵢ(τ) = dᵢ` at every `τ`.
- `g ≥ 1`, descent of `jacDet Φᵢ`:
  - on the Hodge line, `coeff_τ(x) = τ(δ_B x) · coeff_τ(wedge F)`;
  - `δ_B(wedge(p₁^* f, p₂^* h)) = det_u(df) · det_w(dh)` (`det_prod_block`);
  - so `jacDet Φ₁ f = τ(det_u df) · c₁` with `c₁ = jacDet Φ₁ f₁`, and likewise for `Φ₂`;
  - this lets `mkMetrized` define `coeffᵢ τ = τ(δ_u ·) · cᵢ`. Metrization's `JacDetDescends` is not
    needed.
- `g ≥ 1`, heights: indices multiply (as above), coefficients multiply (block Jacobian), and
  covolumes multiply (product-height's `prodLattice_facts`). product-height's `modelHeight_add_of`
  then gives `h(MP) = h(M₁) + h(M₂)`.
- `ProdUnifDeriv` (part `ps_5_analytic`):
  - metrization's `ProductLocalStructure`, restated over the kernel's types, is proved by
    infra-stalks' proof (`productLocalStructureK`);
  - metrization's `prodPts_local`, adapted, gives `productUnifAnalytic`, so `prodUnif` is an
    analytic uniformization;
  - near `0`, `germAlong (prodUnif) (p₁^* t) = germAlong Φ₁ t ∘ blk₁` (metrization's
    `germAlong_eventuallyEq`, copied, with product-height's `evalAt_comp` and
    `prodUnif_eq : prodUnif z = (Φ₁ z₁, Φ₂ z₂) ≫ e⁻¹`);
  - the chain rule then gives the derivative.

## 3. What compiles (all VERIFIED, one Lean process at a time)

| file | contents | result |
|---|---|---|
| `scratch/infra-hodge/ProductHodgeLattice.lean` | `assemble.py`: Prefix (verbatim `scratch/metrization/Metrization.lean` + infra-stalks + hodge-bc2 ExtFrac + infra-smooth-dim SmoothStalk bodies) + `phl_1`–`phl_5` | exit 0, 52 s, 0 errors, no sorry warning, all axiom reports standard |
| `scratch/infra-hodge/ProductSplit.lean` | `assemble_split.py`: SPrefix (`import ZInQKernel.HDecomp.Faltings.H5Neron`, `import Mathlib`, infra-stalks + ExtFrac bodies, verbatim `scratch/product-height/ProductHeight.lean`) + `phl_1`–`phl_3`, `phl_4a` + `ps_1`–`ps_6` | exit 0, 25 s, 0 errors, no sorry warning (one doc-comment mention of the word in the copied header), all axiom reports standard |

`python3 scratch/infra-hodge/verbatim_check.py` prints ALL OK (output in `verbatim_check_out.txt`).
It checks that both Props are character-identical to their owners' definitions:
`ProductHodgeLattice` in metrization's part_prodsplit.lean and in infra-stalks' ProductLocalStructure.lean;
`ProductMetrizationOfProductUnif` in g0-assemble2's a25 part and in product-height's file. It also
checks that every copied block is verbatim. Regenerate with `python3 scratch/infra-hodge/assemble.py` and
`python3 scratch/infra-hodge/assemble_split.py` from the repository root. `ProductSplit.lean` needs
the kernel's `ZInQKernel.HDecomp.Faltings.H5Neron` built.

## 4. Notes for integration

- **Two environments.** metrization's `Metrization.lean` is Mathlib-only, with its own copy of
  `ZInQ.DefFaltings` (`AbVar = DefFaltings.AbVar`). product-height's file imports the kernel
  (`PkgI3.AbVar`). The same declaration names cannot coexist, so the two Props are checked in two
  files. The generic parts `phl_1`–`phl_3`, `phl_4a` compile in both: the line `--IH:ABVAR` becomes
  `open PkgI3 (AbVar)` in the kernel file and is dropped in the metrization file.
- **g0-assemble2.** The field `productMetrizationOfProductUnif` of `GluePieces3` is the same text
  over Leaves.lean's `ZInQ.DefFaltings` copy (`AbVar` through `open DefFaltings`). In that
  environment the parts should be used with `--IH:ABVAR` dropped, together with the Mathlib-only
  infra-stalks/ExtFrac bodies (no name clashes with LPrefix/TailA/TailB: checked by grep).
- New general lemmas worth upstreaming (Mathlib-only, in `phl_3_linalg`): `detIdeal_prod`,
  `idx_mul`, `delta`/`relIndex_detLat`. Also `det_eq_zero_of_rows_supported` (in `ps_1`) and
  `cotMapAt` with its functoriality (in `phl_1`).
- Lean pitfalls (also in the log):
  - `pullback f g` in binder or `Set` positions elaborates in `Type`; write
    `(pullback f g : Scheme)`;
  - instance search does not find `IsLocalRing` for `(Spec ↧ℂ).presheaf.stalk (closedPoint ℂ)`;
    use a helper lemma taking `x : X`;
  - `𝒢.cotangent` versus `CotangentSpace` blocks `rw` with `cotMapAt_comp`; use `exact` with
    explicit terms, or re-introduce `v` at the `CotangentSpace` type.
