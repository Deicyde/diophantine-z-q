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
`scratch/g0-heightadd/HeightAdd.lean` (VERIFIED by `cmp`), which contains
`ZInQ.G0HeightAdd.MetrizationDimUnique`, `MetrizationExists` (from `part_heightadd.lean`) and
`ProductMetrizationGeo` (from `part_prod.lean`) with everything they depend on. None of the three
is false or vacuous.

1. **`MetrizationDimUnique` is proved, with no hypotheses** (VERIFIED):
   ```lean
   theorem ZInQ.Metrization.metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique
   ```
2. **`MetrizationExists` is reduced** to def-faltings' stated `HodgeLatticeTheorem`, one leaf and
   two glue Props (VERIFIED):
   ```lean
   theorem ZInQ.Metrization.metrizationExists_of (hH : HodgeLatticeTheorem)
       (hU : AnalyticUniformizationOfDim) (hJ : JacDetDescends) (hN : JacDetNondegenerate) :
       ZInQ.G0HeightAdd.MetrizationExists
   theorem ZInQ.Metrization.jacDetDescends_of (h : JacDetMultilinear) : JacDetDescends
   ```
3. **`ProductMetrizationGeo` is reduced** to `JacDetDescends` and two glue Props (VERIFIED):
   ```lean
   theorem ZInQ.Metrization.productMetrizationGeo_of' (hJ : JacDetDescends)
       (hPU : ProductUniformization) (hPC : ProductHodgeCompat) :
       ZInQ.G0HeightAdd.ProductMetrizationGeo
   theorem ZInQ.Metrization.productUniformization_of (h : ProductUniformizationAnalytic) :
       ProductUniformization
   ```
   The fourth hypothesis of the first reduction, `ProductLatticeFacts` (product of full lattices,
   covolumes multiply), is proved from Mathlib (`productLatticeFacts`).

With these, g0-heightadd's piece becomes (VERIFIED):

```lean
theorem HSyn.G0Split.heightAdditivity_of_metrization''
    (hN1 : ZInQ.H5Neron.NeronModelExists)                  -- leaf N1 (Néron), as in g0-heightadd
    (h5 : LeafAdopt.H5)                                    -- = HSyn.ResearchLeaves.h5
    (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)   -- stated in def-faltings (not mine)
    (hH : ZInQ.DefFaltings.HodgeLatticeTheorem)            -- stated in def-faltings; reduced by hodge-lattice
    (hUD : ZInQ.Metrization.AnalyticUniformizationOfDim)   -- leaf (uniformization theorem)
    (hJ : ZInQ.Metrization.JacDetMultilinear)              -- glue (calculus)
    (hN : ZInQ.Metrization.JacDetNondegenerate)            -- glue (local coordinates)
    (hPA : ZInQ.Metrization.ProductUniformizationAnalytic) -- glue (products, analytic half)
    (hPC : ZInQ.Metrization.ProductHodgeCompat) :          -- glue (Hodge line of a product)
    HSyn.G0Split.HeightAdditivity
```

g0-heightadd's version needed `MetrizationDimUnique`, `MetrizationExists` and
`ProductMetrizationGeo` as hypotheses; the first is gone and the other two are replaced by
smaller statements whose algebraic parts are proved.

## 1. `MetrizationDimUnique`, proved

Statement (verbatim): two metrizations `M : MetrizedModel A L g`, `M' : MetrizedModel A L g'` with
`M.model = M'.model` have `g = g'`.

Proof (`part_dim.lean`, with `ExtLine.lean`):

- **`g, g' ≥ 1`: pure algebra.** `MetrizedModel` contains `hodge.finrank_eq_one :
  finrank L (hodgeSpace g) = 1`, where `hodgeSpace g = L ⊗_{𝓞_L} ⋀^g_{𝓞_L} C` and `C = 𝔪_ξ/𝔪_ξ²`
  is the same module for both metrizations. `ZInQ.Metrization.eq_of_finrank_one` (new, Mathlib
  only): for a commutative ring `R`, a field `F` that is a flat `R`-algebra and any `R`-module `C`,
  if `F ⊗_R ⋀^g C` and `F ⊗_R ⋀^{g'} C` both have `F`-dimension 1 and `g, g' ≥ 1`, then `g = g'`.
  For `g < g + n` pick `v` with `1 ⊗ v₁ ∧ ⋯ ∧ v_{g+n} ≠ 0` (the `1 ⊗ ιMulti v` span), write
  `v = append a b`, and let `a'`, `b'` be `a`, `b` with their first entries swapped. Right
  multiplication by `ιMulti b` (resp. `ιMulti b'`) in the exterior algebra, base changed to `F`,
  sends `1 ⊗ ιMulti a ↦ 1 ⊗ ιMulti v ≠ 0`, `1 ⊗ ιMulti a' ↦ 0` (resp. `↦ 0`, `↦ −1 ⊗ ιMulti v`), so
  the two vectors are independent, contradicting dimension 1. Flatness of `L` over `𝓞_L`
  (`IsLocalization.flat`) keeps `1 ⊗ ιMulti v ≠ 0` inside `F ⊗ ⋀C`. Mathlib has no base change for
  exterior powers, so this argument avoids it.
- **`g = 0 < g'`: the uniformizations.** `M.arch τ` gives a surjection `Φ : ℂ⁰ → 𝒢(ℂ)_τ`, so
  `𝒢(ℂ)_τ` is a subsingleton. `M'.arch τ` gives `Φ' : ℂ^{g'} → 𝒢(ℂ)_τ` with kernel the discrete
  `M'.hodge.periods τ`; a discrete `ℤ`-submodule of `ℂ^{g'}`, `g' ≥ 1`, is not everything (`ℝ` is
  connected: `t ↦ t·e₁` would be constant), so some `Φ' z ≠ 1`. A number field has an embedding
  `τ : L → ℂ`.

So the argument sketched in def-faltings' `MetrizedModel` docstring is now a proof; it needs
neither the dimension theory of varieties nor the analytic structure of `A(ℂ)`.

## 2. `MetrizationExists`, reduced

Statement (verbatim): every group model `𝒢` of `A_L` has a metrization (`∃ g M, M.model = 𝒢`).

Proved: `exists_metrization_of_dim` builds the metrization at `g = dim A` with lattice
`⋀^g ω_𝒢`, period lattices and coefficient maps from the uniformizations (field by field;
`lattice_eq` is `rfl`). `dim A ∈ ℕ` is `abVar_dim_finite`, proved from g0-dim's `G0Dim.dim_finite`
(copied verbatim into `part_g0dim.lean`). Also proved: `metrized_dim_eq` (every metrization has
`g = dim A`, same hypotheses) and `analyticUniformizationExists_of : AnalyticUniformizationOfDim →
AnalyticUniformizationExists` (the new leaf is not weaker than def-faltings' Prop).

| Prop | Kind | Statement (short) | Why true |
| --- | --- | --- | --- |
| `DefFaltings.HodgeLatticeTheorem` | stated in def-faltings; reduced by hodge-lattice to `TangentDimAtOrigin` and `DimBaseChange` (the latter proved by g0-dim) | `hodgeSpace (dim A)` is a line and `⋀ω_𝒢` a full lattice in it | smoothness (hodge-lattice §4) |
| `Metrization.AnalyticUniformizationOfDim` | **leaf** (published theorem, Lean reformulation over def-faltings' `IsAnalyticUniformization`) | for `g = dim A` and every `τ`: a full lattice `Λ ⊂ ℂ^g` and an analytic uniformization `Φ : ℂ^g → 𝒢(ℂ)_τ` with kernel `Λ` | `A_τ(ℂ)` is a compact connected complex Lie group of dimension `dim A`, hence `ℂ^g/Λ` (Mumford, *Abelian varieties*, §1, UNVERIFIED locator; Serre's GAGA for the analytic structure). It is def-faltings' `AnalyticUniformizationExists` with the dimension pinned |
| `Metrization.JacDetMultilinear` | glue (calculus) | `f ↦ jacDet Φ f` depends only on the classes `df_i`, is additive in each slot, scales by `τ(a)` for `a ∈ 𝓞_L`, and vanishes on equal slots | `Φ 0 = 1` lies over `ξ`; `dom Φ U` open, so `f ∘ Φ` near `0` is independent of the representative; evaluation is a ring map; Leibniz kills `𝔪_ξ²`; row operations on the determinant |
| `Metrization.JacDetDescends` | glue, **proved from `JacDetMultilinear`** (`jacDetDescends_of`) | `jacDet Φ` is the value on wedges of a `τ`-semilinear `hodgeSpace g → ℂ` | universal property of `⋀^g` (`exteriorPower.alternatingMapLinearEquiv`) and `TensorProduct.lift` of `(x, w) ↦ τ(x)·Ψ(w)` |
| `Metrization.JacDetNondegenerate` | glue (complex geometry) | for `g = dim A` and a uniformization with full-lattice kernel, some `f₁, …, f_g ∈ 𝔪_ξ` have `jacDet Φ f ≠ 0` | a regular system of parameters of `𝒪_{A_L,0}` gives holomorphic coordinates at `0` of the complex manifold `A_τ(ℂ)` and `Φ` is a local biholomorphism at `0` (STANDARD) |

`JacDetNondegenerate` is what makes the coefficient map nonzero (`HodgeData.coeff_ne_zero`).
The hypotheses `A.dim = g` and "full lattice" are included only to make it weaker.

## 3. `ProductMetrizationGeo`, reduced

Statement (verbatim): for `IsProductModel eC 𝒢P 𝒢₁ 𝒢₂` and metrizations `M₁`, `M₂` of `𝒢₁`, `𝒢₂`,
there are a metrization `MP` of `𝒢P` of dimension `g₁ + g₂` and nonzero sections `s`, `s₁`, `s₂`
of the three Hodge lattices whose index, coefficients and period covolumes are multiplicative.

New definitions (`part_prodgeo.lean`): `leftBlock`, `rightBlock : ℂ^{g₁+g₂} → ℂ^{gᵢ}`;
`prodLattice Λ₁ Λ₂` (the lattice `Λ₁ × Λ₂` in `Fin.append` coordinates); `prodPts e Φ₁ Φ₂ z =
lift (Φ₁ z') (Φ₂ z'') ≫ e.inv`. `productMetrizationGeo_of` builds `MP` with lattice
`⋀^{g₁+g₂} ω_{𝒢P}`, periods `prodLattice`, uniformization `prodPts e Φ₁ Φ₂` (with `Φᵢ` from
`Mᵢ.arch`) and coefficients from `JacDetDescends`; nonvanishing of the coefficients and
`isLattice` follow from the compatibility in `ProductHodgeCompat`.

| Prop | Kind | Status |
| --- | --- | --- |
| `Metrization.ProductLatticeFacts` | glue (pure Mathlib): `prodLattice Λ₁ Λ₂` is discrete and full, `covol = covol Λ₁ · covol Λ₂` | **proved** (`productLatticeFacts`, also standalone in `ProdLattice.lean`): discreteness by injecting into `Λ₁ × Λ₂`; full rank via `append x 0 + append 0 y`; covolume via the fundamental domain `φ⁻¹(F₁ ×ˢ F₂)` with `φ : ℂ^{g₁+g₂} ≃ ℂ^{g₁} × ℂ^{g₂}` volume preserving (`piCongrLeft` and `sumPiEquivProdPi`) and `Measure.prod_prod` |
| `Metrization.ProductUniformization` | glue: `prodPts e Φ₁ Φ₂` is an analytic uniformization of `𝒢P(ℂ)_τ` with kernel `prodLattice Λ₁ Λ₂` | **reduced** (`productUniformization_of`): the homomorphism, kernel and surjectivity clauses are proved (`prodPts_alg`, from `e`, `MonObj.mul_comp`, `MonObj.one_comp`, `hom_ext`) |
| `Metrization.ProductUniformizationAnalytic` | glue: `dom (prodPts e Φ₁ Φ₂) U` is open and regular functions are holomorphic along `prodPts` | open. Why true: a Zariski open of `𝒢₁ ×_{𝓞_L} 𝒢₂` is covered by basic opens `D(h)` of products `Spec(R₁ ⊗ R₂)` of affine opens; a regular function there is `a/hⁿ`, `a, h` sums of products of functions holomorphic along `Φ₁`, `Φ₂` (STANDARD) |
| `Metrization.ProductHodgeCompat` | glue: `hodgeSpace (g₁+g₂)` of `𝒢P` is a line, and there are nonzero `s`, `s₁`, `s₂` in the lattices with `secIndex` multiplicative such that every coefficient map defined by the Jacobians of `prodPts e Φ₁ Φ₂` has `c s = coeff₁ s₁ · coeff₂ s₂` | open. Why true: `s = p₁*s₁ ∧ p₂*s₂`; `ω_{𝒢P} = p₁*ω₁ ⊕ p₂*ω₂` for a product of smooth group schemes, so `⋀^{top}` is the tensor product of the two lines and indices multiply (norms of ideals); `(p₁*f) ∘ prodPts = f ∘ Φ₁ ∘ leftBlock` near `0`, so the Jacobian is block diagonal (STANDARD) |

A finding on the statement of `ProductMetrizationGeo` (no defect): it asks for *equality*
`MP.hodge.coeff σ s = M₁.hodge.coeff σ s₁ · M₂.hodge.coeff σ s₂`, not of absolute values. This
holds for the product uniformization `prodPts`, but not for an arbitrary metrization of `𝒢P`
with product periods: another uniformization `prodPts ∘ T` with `T(Λ₁ × Λ₂) = Λ₁ × Λ₂` changes
`c s` by `det T`, a complex number of modulus 1. So `MP` must be built from `prodPts`, which is
how `productMetrizationGeo_of` builds it, and `ProductHodgeCompat` is stated for coefficient maps
attached to `prodPts` only.

## 4. Leaves and glue after this task

Leaves (published, cited): N1 `NeronModelExists` and `LeafAdopt.H5` (unchanged, from
g0-heightadd); `AnalyticUniformizationOfDim` (new; the uniformization theorem). Glue, open:
`AnalyticUniformizationUnique` (def-faltings; not one of my targets; bp-analytic's
`IsUniformization.exists_equiv` in `ZInQKernel/HDecomp/Analytic/Uniformization.lean` proves the
analogous statement for its own uniformization structure over `AbVar ℂ`, which might be adapted),
`HodgeLatticeTheorem` (def-faltings; reduced by hodge-lattice), `JacDetMultilinear`,
`JacDetNondegenerate`, `ProductUniformizationAnalytic`, `ProductHodgeCompat`. All of them are
stated over def-faltings' definitions (`GroupModel`, `jacDet`, `IsAnalyticUniformization`,
`detLattice`, `secIndex`), which are built from Mathlib's schemes, stalks, cotangent spaces,
exterior powers and `fderiv`; none mentions heights or the conclusion.

What blocks the open glue is the same Mathlib gap in each case: the compatibility of the
evaluation `evalAt` of regular functions at complex points with restriction, sums, products and
stalks (`JacDetMultilinear`), the complex-manifold structure of `A_τ(ℂ)` (`JacDetNondegenerate`),
and affine covers, stalks and differentials of fibre products of schemes
(`ProductUniformizationAnalytic`, `ProductHodgeCompat`). SPECULATIVE estimate: `JacDetMultilinear`
is the most tractable (a few hundred lines of scheme API).

## 5. Files

- `scratch/metrization/Base.lean`: verbatim copy of `scratch/g0-heightadd/HeightAdd.lean`.
- `scratch/metrization/ExtLine.lean`: `eq_of_finrank_one` (Mathlib only; compiled).
- `scratch/metrization/ProdLattice.lean`: `productLatticeFacts` (Mathlib only; compiled).
- `scratch/metrization/part_dim.lean`, `part_g0dim.lean`, `part_exists.lean`, `part_prodgeo.lean`,
  `part_prodlat.lean`, `part_final.lean`, `part_produnif.lean`, `part_jacdet.lean`: appended to
  `Base.lean` by `build.sh` to give `Metrization.lean`.
- Check: `bash scratch/metrization/build.sh && lake env lean scratch/metrization/Metrization.lean`
  (about 30 s to 2 min with Mathlib loaded).
