# metrization: the three metrization glue Props of g0-heightadd

Status: research note (task metrization, 2026-11-13). Lean: `scratch/metrization/Metrization.lean`
(assembled by `scratch/metrization/build.sh`; self-contained, `import Mathlib` only; compiled with
`lake env lean`, 0 errors, no `sorry`, no `axiom`; every `#print axioms` lists only `propext`,
`Classical.choice`, `Quot.sound`). Two Mathlib-only side files compile on their own:
`scratch/metrization/ExtLine.lean` and `scratch/metrization/ProdLattice.lean`. Results log:
`scratch/metrization/log.md`. Base 2dd83306 (wip/integrate-w36b). No file under `ZInQKernel/` or
`blueprint/` and no other task's file was edited.

Marks: **VERIFIED** = compiled, or read in a file of the repository or of Mathlib. **STANDARD** =
published, with a reference. **SPECULATIVE** = estimate. **UNVERIFIED** = locator from memory (no
network).

## 0. Main result

The three targets are copied verbatim: `scratch/metrization/Base.lean` is byte-identical to
`scratch/g0-heightadd/HeightAdd.lean` (VERIFIED by `cmp`). That file contains
`ZInQ.G0HeightAdd.MetrizationDimUnique` and `MetrizationExists` (from `part_heightadd.lean`) and
`ProductMetrizationGeo` (from `part_prod.lean`), with everything they depend on. None of the three
is false or vacuous.

1. **`MetrizationDimUnique` is proved, with no hypotheses** (VERIFIED):
   ```lean
   theorem ZInQ.Metrization.metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique
   ```
2. **`MetrizationExists` is reduced to def-faltings' stated `HodgeLatticeTheorem`, one leaf and
   one glue Prop** (VERIFIED):
   ```lean
   theorem ZInQ.Metrization.metrizationExists_of' (hH : HodgeLatticeTheorem)
       (hU : AnalyticUniformizationOfDim) (hN : JacDetNondegenerate) :
       ZInQ.G0HeightAdd.MetrizationExists
   ```
   On the way, the glue Prop `JacDetDescends` (the Jacobian determinant `jacDet Φ` is the value on
   wedges of a `τ`-semilinear map on the Hodge line) is **proved outright**
   (`ZInQ.Metrization.jacDetDescends`), from Mathlib's scheme API and calculus.
3. **`ProductMetrizationGeo` is reduced to two glue Props of algebraic geometry, with no
   analysis left in them** (VERIFIED):
   ```lean
   theorem ZInQ.Metrization.productMetrizationGeo_of_local (hLS : ProductLocalStructure)
       (hPL : ProductHodgeLattice) : ZInQ.G0HeightAdd.ProductMetrizationGeo
   ```
   Proved on the way: `ProductLatticeFacts` (the product of full lattices is a full lattice and
   covolumes multiply), the algebraic half of the product uniformization (`prodPts_alg`), its
   analytic half from `ProductLocalStructure` (`productUniformizationAnalytic_of`),
   `ProductJacobian` (the Jacobian of the product uniformization is block diagonal), and
   `JacDetDescends`.

With these, g0-heightadd's piece `HeightAdditivity` becomes (VERIFIED):

```lean
theorem HSyn.G0Split.heightAdditivity_of_metrization_v3
    (hN1 : ZInQ.H5Neron.NeronModelExists)                  -- leaf N1 (Néron), as in g0-heightadd
    (h5 : LeafAdopt.H5)                                    -- = HSyn.ResearchLeaves.h5
    (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)   -- stated in def-faltings (not a target here)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)            -- stated in def-faltings; reduced by hodge-lattice
    (hUD : ZInQ.Metrization.AnalyticUniformizationOfDim)   -- leaf (the uniformization theorem)
    (hN : ZInQ.Metrization.JacDetNondegenerate)            -- glue (local parameters are coordinates)
    (hLS : ZInQ.Metrization.ProductLocalStructure)         -- glue (affine product charts, at ℂ-points)
    (hPL : ZInQ.Metrization.ProductHodgeLattice) :         -- glue (Hodge lattice of a product)
    HSyn.G0Split.HeightAdditivity
```

g0-heightadd's version (`heightAdditivity_of_geo`) had `MetrizationDimUnique`,
`MetrizationExists` and `ProductMetrizationGeo` as hypotheses. The first is now a theorem. The
other two are replaced by `AnalyticUniformizationOfDim`, `JacDetNondegenerate`,
`ProductLocalStructure` and `ProductHodgeLattice`. All the calculus and linear algebra in between
is proved; each of the four remaining Props needs a piece of algebraic or complex geometry that
Mathlib lacks (§4).

## 1. `MetrizationDimUnique`, proved

Statement (verbatim): if `M : MetrizedModel A L g` and `M' : MetrizedModel A L g'` have
`M.model = M'.model`, then `g = g'`.

Proof (`part_dim.lean`, with `ExtLine.lean`):

- **`g, g' ≥ 1`: pure algebra.** `MetrizedModel` contains `hodge.finrank_eq_one :
  finrank L (hodgeSpace g) = 1`, where `hodgeSpace g = L ⊗_{𝓞_L} ⋀^g_{𝓞_L} C` and `C = 𝔪_ξ/𝔪_ξ²`
  is the same module for both metrizations. The new lemma `ZInQ.Metrization.eq_of_finrank_one`
  (Mathlib only) says: for a commutative ring `R`, a field `F` that is a flat `R`-algebra and any
  `R`-module `C`, if `F ⊗_R ⋀^g C` and `F ⊗_R ⋀^{g'} C` both have `F`-dimension 1 and
  `g, g' ≥ 1`, then `g = g'`. Proof for `g < g + n`: pick `v` with `1 ⊗ v₁ ∧ ⋯ ∧ v_{g+n} ≠ 0`
  (such tensors span). Write `v = append a b`, and let `a'`, `b'` be `a`, `b` with their first
  entries swapped. Right multiplication by `ιMulti b` (resp. `ιMulti b'`) in the exterior algebra,
  base changed to `F`, sends `1 ⊗ ιMulti a ↦ 1 ⊗ ιMulti v ≠ 0` and `1 ⊗ ιMulti a' ↦ 0`
  (resp. `↦ 0` and `↦ −1 ⊗ ιMulti v`). So the two vectors are independent, which contradicts
  dimension 1. `L` is flat over `𝓞_L` (`IsLocalization.flat`), so `1 ⊗ ιMulti v` stays nonzero in
  `F ⊗ ⋀C`. Mathlib has no base change for exterior powers; the argument avoids it.
- **`g = 0 < g'`: the uniformizations.** `M.arch τ` gives a surjection `Φ : ℂ⁰ → 𝒢(ℂ)_τ`, so
  `𝒢(ℂ)_τ` has at most one point. `M'.arch τ` gives `Φ' : ℂ^{g'} → 𝒢(ℂ)_τ` with kernel the discrete
  lattice `M'.hodge.periods τ`. A discrete `ℤ`-submodule of `ℂ^{g'}` with `g' ≥ 1` is not all of
  `ℂ^{g'}` (`ℝ` is connected, so `t ↦ t·e₁` would be constant), so some `Φ' z ≠ 1`. A number field
  has an embedding `τ : L → ℂ`.

So the argument sketched in def-faltings' `MetrizedModel` docstring is now a proof. It uses
neither the dimension theory of varieties nor the analytic structure of `A(ℂ)`.

## 2. `MetrizationExists`, reduced

Statement (verbatim): every group model `𝒢` of `A_L` has a metrization (`∃ g M, M.model = 𝒢`).

Proved: `exists_metrization_of_dim` builds the metrization at `g = dim A` field by field:
lattice `⋀^g ω_𝒢` (so `lattice_eq` is `rfl`), period lattices and uniformizations from
`AnalyticUniformizationOfDim`, coefficient maps from `jacDetDescends`. `dim A ∈ ℕ` is
`abVar_dim_finite`, proved from g0-dim's `G0Dim.dim_finite` (copied verbatim into
`part_g0dim.lean`). Also proved: `metrized_dim_eq` (every metrization has `g = dim A`, under the
same hypotheses) and `analyticUniformizationExists_of : AnalyticUniformizationOfDim →
AnalyticUniformizationExists`, so the new leaf is not weaker than def-faltings' Prop.

**`JacDetDescends` is proved** (`part_jacdet.lean`, `part_jacgerm.lean`, `part_jacscalar.lean`,
`part_jacclass.lean`), in two layers:
- `jacDetDescends_of : JacDetMultilinear → JacDetDescends` (algebra): choose lifts through
  `toCotangent` (`Function.surjInv`), build the alternating map, pass to `⋀^g`
  (`exteriorPower.alternatingMapLinearEquiv`), extend scalars along `τ`
  (`TensorProduct.lift` of `(x, w) ↦ τ(x)·Ψ(w)`).
- The four clauses of `JacDetMultilinear` (class invariance, slot additivity, scaling by `τ(a)`,
  vanishing on equal slots) are proved from facts about evaluation at complex points:
  `ptC_hom_apply` and `one_left_apply` (the identity complex point lies over `ξ`),
  `zero_mem_dom`, `evalAt_res`, `evalAt_add`, `evalAt_mul`, `germAlong_eventuallyEq`
  (`germAlong Φ t` agrees near `0` with the function of any representative of `t`),
  `evalAt_structSection` (the image of `a ∈ 𝓞_L` evaluates to `τ(a)`, by `ΓSpecIso_naturality`),
  and `evalAt_one_eq_zero` (a section with germ in `𝔪_ξ` vanishes at the identity point: the
  stalk map to the stalk of `Spec ℂ`, a field, is local, and `germ_injective_of_isIntegral`). Then
  `d(germAlong Φ t)(0) = 0` for `t ∈ 𝔪_ξ²` (Leibniz, induction on `𝔪 · 𝔪`), and the row
  operations on the determinant follow.

| Prop | Kind | Statement (short) | Why true |
| --- | --- | --- | --- |
| `DefFaltings.HodgeLatticeTheorem` | stated in def-faltings; reduced by hodge-lattice to `TangentDimAtOrigin` and `DimBaseChange` (the latter proved by g0-dim) | `hodgeSpace (dim A)` is a line and `⋀ω_𝒢` is a full lattice in it | smoothness (hodge-lattice §4) |
| `Metrization.AnalyticUniformizationOfDim` | **leaf** (published theorem, restated over def-faltings' `IsAnalyticUniformization`) | for `g = dim A` and every `τ`: a full lattice `Λ ⊂ ℂ^g` and an analytic uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` with kernel `Λ` | `A_τ(ℂ)` is a compact connected complex Lie group of dimension `dim A`, hence `ℂ^g/Λ` (Mumford, *Abelian varieties*, §1, UNVERIFIED locator; Serre's GAGA for the analytic structure). It is def-faltings' `AnalyticUniformizationExists` with the dimension pinned |
| `Metrization.JacDetNondegenerate` | glue (complex geometry) | for `g = dim A` and a uniformization whose kernel is a full lattice, some `f₁, …, f_g ∈ 𝔪_ξ` have `jacDet Φ f ≠ 0` | a regular system of parameters of `𝒪_{A_L,0}` gives holomorphic coordinates at `0` on the complex manifold `A_τ(ℂ)`, and `Φ` is a local biholomorphism at `0`: it is continuous for the analytic topology (regular functions are holomorphic along it), so it lifts a linear map of `ℂ^g` that is complex (holomorphy) and injective (discrete kernel) (STANDARD) |

`JacDetNondegenerate` makes the coefficient maps nonzero (`HodgeData.coeff_ne_zero`). The
hypotheses `A.dim = g` and "full lattice" are there only to make it weaker.

## 3. `ProductMetrizationGeo`, reduced

Statement (verbatim): for `IsProductModel eC 𝒢P 𝒢₁ 𝒢₂` and metrizations `M₁`, `M₂` of `𝒢₁`, `𝒢₂`,
there are a metrization `MP` of `𝒢P` of dimension `g₁ + g₂` and nonzero sections `s`, `s₁`, `s₂`
of the three Hodge lattices whose index, coefficients and period covolumes are multiplicative.

New definitions (`part_prodgeo.lean`, `part_prodsplit.lean`): `leftBlock` and
`rightBlock : ℂ^{g₁+g₂} → ℂ^{gᵢ}`; `prodLattice Λ₁ Λ₂` (the lattice `Λ₁ × Λ₂` in `Fin.append`
coordinates); `prodPts e Φ₁ Φ₂ z = lift (Φ₁ z') (Φ₂ z'') ≫ e.inv`; `pullGerm φ : 𝒪_{ℋ,ξ} → 𝒪_{𝒢,ξ}`
(pull-back of germs along a homomorphism of group models, using `φ(ξ) = ξ`, proved as
`map_genericUnit_of_isMonHom`). `productMetrizationGeo_of` builds `MP` with lattice
`⋀^{g₁+g₂} ω_{𝒢P}`, periods `prodLattice`, uniformization `prodPts e Φ₁ Φ₂` (with `Φᵢ` from
`Mᵢ.arch`) and coefficients from `jacDetDescends`.

| Prop | Kind | Status |
| --- | --- | --- |
| `Metrization.ProductLatticeFacts` | glue (pure Mathlib): `prodLattice Λ₁ Λ₂` is discrete and full, and `covol = covol Λ₁ · covol Λ₂` | **proved** (`productLatticeFacts`, also standalone in `ProdLattice.lean`). Discreteness: inject into `Λ₁ × Λ₂`. Full rank: `append x 0 + append 0 y`. Covolume: the fundamental domain `φ⁻¹(F₁ ×ˢ F₂)`, where `φ : ℂ^{g₁+g₂} ≃ ℂ^{g₁} × ℂ^{g₂}` preserves volume (`piCongrLeft`, `sumPiEquivProdPi`), and `Measure.prod_prod` |
| `Metrization.ProductUniformization` | glue: `prodPts e Φ₁ Φ₂` is an analytic uniformization of `𝒢P(ℂ)_τ` with kernel `prodLattice Λ₁ Λ₂` | **reduced** to `ProductUniformizationAnalytic` (`productUniformization_of`). The homomorphism, kernel and surjectivity clauses are proved (`prodPts_alg`, from `e`, `MonObj.mul_comp`, `MonObj.one_comp`, `hom_ext`) |
| `Metrization.ProductUniformizationAnalytic` | glue: each `dom (prodPts e Φ₁ Φ₂) U` is open and regular functions are holomorphic along `prodPts` | **reduced** to `ProductLocalStructure` (`productUniformizationAnalytic_of`, via `prodPts_local`: near each point of `dom`, the open set `{z ∈ dom Φ₁ V₁ × dom Φ₂ V₂ : H(z) ≠ 0}` lies in `dom` and the function is the holomorphic quotient `A/H`) |
| `Metrization.ProductLocalStructure` | glue (algebraic geometry at complex points, no analysis) | **open**. Statement: for `e : 𝒢P ≅ 𝒢₁ × 𝒢₂`, an open `U ⊂ 𝒢P`, `s ∈ Γ(U)` and complex points `p₁`, `p₂` with `e⁻¹(p₁, p₂) ∈ U(ℂ)`, there are opens `Vᵢ ∋ pᵢ` and regular functions `a_k, c_k` on `V₁`, `b_k, d_k` on `V₂` with `H = Σ c_k(·) d_k(·) ≠ 0` at `(p₁, p₂)`, and wherever `H(p₁', p₂') ≠ 0` on `V₁(ℂ) × V₂(ℂ)`: `e⁻¹(p₁', p₂') ∈ U(ℂ)` and `s(e⁻¹(p₁', p₂')) · H = Σ a_k(p₁') b_k(p₂')`. Why true: affine `Vᵢ = Spec Rᵢ` give the open `Spec(R₁ ⊗ R₂)` of the product; a basic open `D(h) ∋ (p₁, p₂)` inside `e(U)`; `s = a/h^m` there; `H = h^m` (STANDARD) |
| `Metrization.ProductHodgeCompat` | glue: the Hodge line of `𝒢P` with a product section whose coefficient is the product | **reduced** (`productHodgeCompat_of`) to `ProductUniformization`, `ProductHodgeLattice` and `ProductJacobian` |
| `Metrization.ProductJacobian` | glue (calculus): `jacDet (prodPts e Φ₁ Φ₂) (p₁*f₁, p₂*f₂) = jacDet Φ₁ f₁ · jacDet Φ₂ f₂` | **proved** (`productJacobian`): `pullGerm_germ`, `evalAt_comp`, `(p₁*t) ∘ prodPts = (t ∘ Φ₁) ∘ leftBlock` near `0`, chain rule, `reindex finSumFinEquiv` and `det_fromBlocks_zero₂₁` |
| `Metrization.ProductHodgeLattice` | glue (algebra) | **open**. Statement: `hodgeSpace (g₁+g₂)` of `𝒢P` is a line, and there are germ tuples `f₁`, `f₂`, their pull-backs `f = (p₁*f₁, p₂*f₂)` and `a₁, a₂ ∈ L` with `sᵢ = aᵢ · 1⊗dfᵢ` nonzero in `⋀ω_{𝒢ᵢ}`, `s = a₁a₂ · 1⊗df` nonzero in `⋀ω_{𝒢P}`, and `[⋀ω_{𝒢P} : 𝓞s] = [⋀ω₁ : 𝓞s₁]·[⋀ω₂ : 𝓞s₂]`. Why true: `ω_{𝒢P} = p₁*ω₁ ⊕ p₂*ω₂` and `𝔪_ξ/𝔪_ξ² = p₁*C₁ ⊕ p₂*C₂` for a product of smooth group schemes, so `⋀^{top}` is the tensor product of the two lines, and indices multiply for invertible `𝓞_L`-modules (norms of ideals) (STANDARD; EGA IV 17.2.3, UNVERIFIED locator) |

A finding about the statement of `ProductMetrizationGeo` (not a defect): it asks for equality
`MP.hodge.coeff σ s = M₁.hodge.coeff σ s₁ · M₂.hodge.coeff σ s₂`, not just equality of absolute
values. This holds for the product uniformization `prodPts`, but not for an arbitrary metrization
of `𝒢P` with product periods: another uniformization `prodPts ∘ T` with `T(Λ₁ × Λ₂) = Λ₁ × Λ₂`
multiplies `c s` by `det T`, a complex number of modulus 1. So `MP` has to be built from `prodPts`,
which is what `productMetrizationGeo_of` does.

## 4. Leaves and glue after this task

Inputs of `heightAdditivity_of_metrization_v2`:
- Leaves (published, cited): N1 `NeronModelExists` and `LeafAdopt.H5` (unchanged from
  g0-heightadd), and `AnalyticUniformizationOfDim` (new; the uniformization theorem).
- Stated in def-faltings, not targets of this task: `AnalyticUniformizationUnique` (bp-analytic's
  `IsUniformization.exists_equiv` in `ZInQKernel/HDecomp/Analytic/Uniformization.lean` proves the
  analogous statement for its own uniformization structure over `AbVar ℂ` and might be adapted)
  and `HodgeLatticeTheorem` (reduced by hodge-lattice).
- New glue, open: `JacDetNondegenerate`, `ProductLocalStructure`, `ProductHodgeLattice`.

All of them are stated over def-faltings' definitions (`GroupModel`, `jacDet`, `evalAt`,
`IsAnalyticUniformization`, `detLattice`, `secIndex`) and the new `prodPts`, `prodLattice`,
`pullGerm`, which are built from Mathlib's schemes, stalks, cotangent spaces, exterior powers and
`fderiv`. None mentions heights or the conclusion.

What blocks each open glue Prop is missing from Mathlib: the complex-manifold structure of
`A_τ(ℂ)` (local parameters as holomorphic coordinates) for `JacDetNondegenerate`; affine opens of
fibre products of schemes with their rings `R₁ ⊗ R₂`, and sections on basic opens, for
`ProductLocalStructure`; stalks and differentials of fibre products for `ProductHodgeLattice`.
SPECULATIVE estimate: `ProductLocalStructure` is the most tractable of the three (Mathlib has
`pullbackSpecIso`); it is pure scheme theory.

## 5. Files

- `scratch/metrization/Base.lean`: verbatim copy of `scratch/g0-heightadd/HeightAdd.lean`.
- `scratch/metrization/ExtLine.lean`: `eq_of_finrank_one` (Mathlib only; compiled).
- `scratch/metrization/ProdLattice.lean`: `productLatticeFacts` (Mathlib only; compiled).
- `scratch/metrization/part_*.lean` (`dim`, `g0dim`, `exists`, `prodgeo`, `prodlat`, `final`,
  `produnif`, `jacdet`, `prodsplit`, `jacgerm`, `jacscalar`, `jacclass`, `prodjac`, `produnif2`):
  appended to `Base.lean` in this order by `build.sh` to give `Metrization.lean` (about 5000
  lines).
- `scratch/metrization/build_integrated.sh`: integration check. It appends the same parts to
  g0-heightadd's `SplitIntegrated.lean` (g0-split's `Split.lean`, the full leaf-bundle file, with
  g0-heightadd's proofs) and closes `HSyn.G0Split.HeightAdditivity` with `r.h5` from
  `HSyn.ResearchLeaves` (generated file `SplitMetrization.lean`, not committed; needs
  `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant` first).
- Check: `bash scratch/metrization/build.sh && lake env lean scratch/metrization/Metrization.lean`
  (about 30 s once Mathlib is loaded; prerequisites as for g0-heightadd: none beyond Mathlib).
