# g0-heightadd: the glue piece `HeightAdditivity` (E4)

Status: research note (task g0-heightadd, 2026-11-13). Lean: `scratch/g0-heightadd/HeightAdd.lean`
(self-contained, `import Mathlib` only; compiled; no `sorry`, no `axiom`; every `#print axioms`
lists only `propext`, `Classical.choice`, `Quot.sound`). Results log: `scratch/g0-heightadd/log.md`.
No file under `ZInQKernel/` or `blueprint/` and no other task's file was edited. Base 883c4ddf
with origin/wip/g0-split (c20fa62b) and origin/wip/h5-neron (b7c1dc21) merged in (neither was in
the base).

Marks: **VERIFIED** = compiled, or read in a file of the repository or of Mathlib. **STANDARD** =
published, with a reference. **SPECULATIVE** = estimate. **UNVERIFIED** = locator from memory (no
network).

## 0. Main result

**The piece is neither false nor vacuous. It is proved in Lean, word for word as g0-split states
it, from one new leaf, one field of the leaf bundle, one Prop that def-faltings already states,
and three new glue Props** (VERIFIED, compiled):

```lean
theorem HSyn.G0Split.heightAdditivity_of_geo
    (hN1 : ZInQ.H5Neron.NeronModelExists)                  -- leaf N1 (Néron)
    (h5 : LeafAdopt.H5)                                    -- = HSyn.ResearchLeaves.h5
    (hU : ZInQ.DefFaltings.AnalyticUniformizationUnique)   -- glue, stated in def-faltings
    (hD : ZInQ.G0HeightAdd.MetrizationDimUnique)           -- glue, new
    (hE : ZInQ.G0HeightAdd.MetrizationExists)              -- glue, new
    (hG : ZInQ.G0HeightAdd.ProductMetrizationGeo) :        -- glue P2a-geo, new
    HSyn.G0Split.HeightAdditivity
```

Two coarser forms are proved on the way (VERIFIED):
- `heightAdditivity_of (hN1) (h5) (hH : ZInQ.H5Neron.ProductModelHeight)`, with glue P2 as one
  hypothesis;
- `heightAdditivity_of_split (hN1) (h5) (hU) (hD) (hE) (hP : ProductMetrization)`, with P2a
  whole.

They are connected by `productModelHeight_of : U → MetrizationDimUnique → MetrizationExists →
ProductMetrization → ProductModelHeight` and `productMetrization_of_geo : ProductMetrizationGeo →
ProductMetrization`. The second is the Arakelov-degree computation `modelHeight_add_of`: Hodge data
whose index, coefficients and covolumes are multiplicative have additive model heights.

`HeightAdditivity`, `IsProductOf` and `LeafAdopt.H5` are copied verbatim from
`scratch/g0-split/Split.lean`. So are the definitions they use: lines 16667-18603 of that file,
which are def-faltings' `ZInQ.DefFaltings`, copied unchanged as `Prefix.lean`. So the theorem is
about the same Prop. An integration check pastes the proofs into a copy of `Split.lean` and closes
the piece there with `r.h5`: `scratch/g0-heightadd/SplitIntegrated.lean` (both `heightAdditivity_of_split` and `heightAdditivity_of_geo`) compiled in 3 min
with 0 errors, and its `#print axioms` lists only the three standard axioms (VERIFIED).

**The gap is not closed.** The four glue hypotheses U, `MetrizationDimUnique`,
`MetrizationExists` and `ProductMetrizationGeo` are true (STANDARD, §3) but unproved. Each needs
theory that Mathlib v4.35 lacks: the stalk of a fibre product of schemes, the rank of the
cotangent space of a smooth group scheme, and the complex-analytic uniformization of `A(ℂ)`.

## 1. Is h5-neron's `stableFaltingsHeight_add_le'` exactly the piece? No; three gaps, all closed

`stableFaltingsHeight_add_le' (hN1) (hmin : NeronModelMinimal) (hH : ProductModelHeight) A B C
(hC : IsProductAbVar C A B) : h(A) + h(B) ≤ h(C)` (h5-neron, compiled there) differs from
`HeightAdditivity` in three ways:

| # | h5-neron | the piece | closed by |
|---|---|---|---|
| (i) | over `PkgI3.AbVar` (the kernel's `Objects.lean`, via `ZInQKernel.HDecomp.Faltings`) | over `ZInQ.DefFaltings.AbVar` (the second copy of the same structure in `Split.lean`) | h5-neron's parts A and E recompiled **unchanged** over `DefFaltings.AbVar`. Only the line `open PkgI3 (AbVar)` was dropped (VERIFIED) |
| (ii) | `IsProductAbVar C A B`: an iso `e : C ≅ A ⊗ B` whose components are homomorphisms | `IsProductOf P.X A.X Z.X`: homomorphisms `p₁, p₂` with `lift p₁ p₂` an iso | `isProductAbVar_of_isProductOf`, proved (`e := asIso (lift p₁ p₂)`) |
| (iii) | inequality in `EReal` | `∀ a z p : ℝ, h(A) = a → h(Z) = z → h(P) = p → a + z ≤ p` | `EReal.coe_add`, `EReal.coe_le_coe_iff` |

The remaining hypotheses are of three kinds. `NeronModelMinimal` is the second component of
`LeafAdopt.H5 = StableHeightFinite ∧ NeronModelMinimal`, which is the field `h5` of
`HSyn.ResearchLeaves`, so it is already in the bundles. N1 (`NeronModelExists`) is not in the
bundles. `TextbookLeaves.t3` (`PkgI2.NeronMappingAbelianScheme`) covers only abelian schemes, so N1
is a new leaf. `ProductModelHeight` is glue P2.

h5-neron's finding was that this direction needs no semistable reduction, because the comparison
is made over each field `L` separately. That stays true: only the per-field `NeronModelMinimal` is
used, so h5-neron's caveat (a) about `LeafAdopt.H5` (base change across fields) does not affect E4.

## 2. The proof (all VERIFIED, compiled)

1. Fix `P ≅ A × Z` (`IsProductOf`). Since `h(P) = inf_{L, 𝒢} h(𝒢)` (`stableFaltingsHeight_eq_iInf_height`),
   it suffices to show `h(A) + h(Z) ≤ h(𝒢)` for every number field `L ⊇ K` and every group model `𝒢`
   of `P_L`.
2. By N1, `A_L` and `Z_L` have Néron models `𝒩₁, 𝒩₂` over `𝓞_L`. Their fibre product is a group
   model `𝒩P` of `P_L` (`productGroupModelExists`, glue P1, proved by h5-neron). It is a Néron model
   (`isNeronModel_of_isProductModel`, from `NeronProp.tensor`, proved by h5-neron).
3. By `NeronModelMinimal` (`r.h5.2`), `h(𝒩P) ≤ h(𝒢)`. By `ProductModelHeight`,
   `h(𝒩₁) + h(𝒩₂) ≤ h(𝒩P)`. By definition, `h(A) ≤ h(𝒩₁)` and `h(Z) ≤ h(𝒩₂)`.
4. **`ProductModelHeight` from four Props** (`productModelHeight_of`, new). Given `𝒢P ≅ 𝒢₁ × 𝒢₂`,
   take metrizations `M₁` of `𝒢₁` and `M₂` of `𝒢₂` (`MetrizationExists`). Then
   `ProductMetrization` gives a metrization `MP` of `𝒢P` of dimension `g₁ + g₂` with
   `h(MP) = h(M₁) + h(M₂)`. Every metrization of `𝒢P` has dimension `g₁ + g₂`
   (`MetrizationDimUnique`) and, by U, the same height as `MP`
   (`MetrizedModel.modelHeight_eq_of_model_eq`, def-faltings). Hence `h(𝒢P) = h(MP)`
   (`le_height_of_model`, `height_le_of_model`), and
   `h(𝒢₁) + h(𝒢₂) ≤ h(M₁) + h(M₂) = h(MP) = h(𝒢P)`.
5. **`ProductMetrization` from `ProductMetrizationGeo`** (`productMetrization_of_geo`, new).
   Faltings' formula gives
   `h(D) = [L:ℚ]⁻¹(log #(Λ/𝓞s) − ½ Σ_σ log(|coeff_σ s|² covol(periods σ)))` for any nonzero
   section `s` (`HodgeData.modelHeight_eq`, def-faltings). So multiplicativity of index,
   coefficients and covolumes makes the heights add (`modelHeight_add_of`).

## 3. The hypotheses: leaf or glue, and why each is believed true

| name | kind | statement (informal) | source / why true | status |
|---|---|---|---|---|
| `H5Neron.NeronModelExists` (N1) | **leaf** (new, not in the bundles) | for `A/K` and a number field `L ⊇ K` there is a group model `𝒩` of `A_L` over `𝓞_L` with the Néron mapping property | Néron; Bosch-Lütkebohmert-Raynaud, *Néron models*, §1.4 Thm 3 (existence over a Dedekind base), with the definition §1.2 Def. 1. The group law extends by the mapping property (§1.2) (locators UNVERIFIED). A Néron model is smooth, separated and of finite type, hence quasi-compact over the noetherian `Spec 𝓞_L` | unproved (leaf) |
| `LeafAdopt.H5` (only `.2 = NeronModelMinimal` used) | **leaf** (bundle field `ResearchLeaves.h5`) | over each `L`, a Néron model has the least height among group models | Faltings 1983 §1; BLR 1.2/1. `𝒢 → 𝒩` gives `ω_𝒩 ⊆ ω_𝒢` and smaller degree (locators UNVERIFIED) | in the bundle |
| `DefFaltings.AnalyticUniformizationUnique` (U) | glue (already stated in def-faltings, `Models.lean`) | two analytic uniformizations of `𝒢(ℂ)_τ` differ by a `ℂ`-linear automorphism | a holomorphic homomorphism of complex tori lifts to a linear map (STANDARD; Mumford, *Abelian varieties* §1, UNVERIFIED) | unproved |
| `G0HeightAdd.MetrizationDimUnique` | glue (new) | two metrizations of one group model have the same `g` | both equal `dim A`. For `0 < g ≠ dim A`, `⋀^g ω` is not a line. `g = 0` is excluded for `dim A ≥ 1` because `Φ : ℂ⁰ → A_τ(ℂ)` would be onto (the argument of def-faltings' `MetrizedModel` docstring; STANDARD) | unproved |
| `G0HeightAdd.MetrizationExists` | glue (new; correctness of def-faltings' definition) | every group model `𝒢` of `A_L` has a metrization | `HodgeLatticeTheorem` and `AnalyticUniformizationExists` (both stated in def-faltings), with `coeff_τ(1 ⊗ df) = jacDet Φ f`. This is `LeafAdopt.H5`'s caveat (nonempty index set), for each model | unproved |
| `G0HeightAdd.ProductMetrization` (P2a) | glue (new) | metrizations of `𝒢₁` and `𝒢₂` (dimensions `g₁`, `g₂`) give one of `𝒢P ≅ 𝒢₁ × 𝒢₂` of dimension `g₁ + g₂` whose height is the sum | `ω_{𝒢₁×𝒢₂} = ω₁ ⊕ ω₂`; `⋀^{g₁+g₂}(ω₁ ⊕ ω₂) = ⋀^{g₁}ω₁ ⊗ ⋀^{g₂}ω₂`; `Φ₁ × Φ₂` is a uniformization with kernel `Λ₁ × Λ₂`; `jacDet` and `covol` are multiplicative; the Arakelov degree is additive on tensor products of Hermitian lines (Faltings 1983 §1; Deligne, Sém. Bourbaki 616 §1; STANDARD, locators UNVERIFIED) | proved from P2a-geo (`productMetrization_of_geo`, via `modelHeight_add_of`) |
| `G0HeightAdd.ProductMetrizationGeo` (P2a-geo) | glue (new) | for `𝒢P ≅ 𝒢₁ × 𝒢₂` and metrizations `M₁`, `M₂`: a metrization `MP` of `𝒢P` of dimension `g₁ + g₂`, with nonzero sections `s`, `s₁`, `s₂` of the three Hodge lattices whose index, coefficients `coeff σ` and period covolumes multiply | `s = p₁*s₁ ∧ p₂*s₂`; `⋀^{top}(ω₁ ⊕ ω₂) = ⋀ω₁ ⊗ ⋀ω₂`; norms of ideals multiply; `Φ₁ × Φ₂` (coordinates `Fin.append`) has lattice `Λ₁ × Λ₂` and a block-diagonal Jacobian (STANDARD) | unproved |
| `H5Neron.ProductModelHeight` (P2) | glue | `h(𝒢₁) + h(𝒢₂) ≤ h(𝒢P)` | follows from the four rows above (`productModelHeight_of`, proved) | proved from U, DimUnique, Exists, P2a |

Proved parts that the table relies on (VERIFIED, compiled here):
- P1 `productGroupModelExists`, `NeronProp.tensor`, `isNeronModel_of_isProductModel` (h5-neron);
- `isProductAbVar_of_isProductOf`, `height_le_of_model`, `le_height_of_model`,
  `productModelHeight_of`, `modelHeight_add_of`, `productMetrization_of_geo` (new).

The Arakelov-degree part of P2a is proved for general Hodge data (`modelHeight_add_of`, from
Faltings' formula `HodgeData.modelHeight_eq`). What is left in P2a-geo is purely geometric:
constructing the product metrization and the three multiplicativities.

**Consistency in dimension 0** (the only abelian variety Mathlib v4.35 can construct; §4). The
three new glue Props hold for `A = B = C = 0` (`Spec K`), and every hypothesis of
`ProductMetrization` is allowed there. So they are at least not contradictory where they can be
tested: `metrizationExists_zero`, `metrizationDimUnique_zero` and `productMetrization_zero`
(VERIFIED, compiled).

## 4. Files

- `scratch/g0-heightadd/Prefix.lean`: `import Mathlib`, then `Split.lean` l. 16667-18603 verbatim
  (def-faltings). Compiles standalone in 93 s (VERIFIED).
- `scratch/g0-heightadd/part_heightadd.lean`: h5-neron parts A and E over `DefFaltings.AbVar`;
  the verbatim copies of `LeafAdopt.H5`, `G0Split.IsProductOf` and `G0Split.HeightAdditivity`;
  the bridge; `heightAdditivity_of`; the P2 split; `heightAdditivity_of_split`.
- `scratch/g0-heightadd/part_zero.lean`: the dimension-0 consistency check. It contains
  `AbVar.zero` for def-faltings' structure, copied from `PkgI3.AbVar.zero`, and h5-neron's part B.
- `scratch/g0-heightadd/part_prod.lean`: `modelHeight_add_of`, `ProductMetrizationGeo`,
  `productMetrization_of_geo`, `heightAdditivity_of_geo`.
- `scratch/g0-heightadd/HeightAdd.lean` = `Prefix.lean` + the three parts (`build.sh`). Check with
  `lake env lean scratch/g0-heightadd/HeightAdd.lean`.
- `scratch/g0-heightadd/SplitIntegrated.lean` (`build_integrated.sh`): `Split.lean` with the
  proofs inserted. h5-neron's Néron part goes after the def-faltings section, and the bridge, the
  P2 split and an `example` closing `HSyn.G0Split.HeightAdditivity` from `r.h5` go at the end.
  Its build first needs `lake build ZInQKernel.Hypotheses.JHeight
  ZInQKernel.Compiler.Precision.HeightConstant`.

## 5. Integration

In `Split.lean`, the field `additivity : HeightAdditivity` of `G0Split.MissingPieces` can be
replaced by the leaf N1 (`NeronModelExists`) and the four glue Props U, `MetrizationDimUnique`,
`MetrizationExists`, `ProductMetrizationGeo`, with
`additivity := heightAdditivity_of_geo hN1 r.h5 hU hD hE hG`. N1 then joins the leaf
count as a new research/textbook leaf (BLR 1.4/3). The paste is exactly what
`SplitIntegrated.lean` does. That file compiled with 0 errors (3 min, log runs 3 and 6), and
`heightAdditivity_of_split`, `heightAdditivity_of_geo`, `glueOutputs_of_leaves` and `sixContactMin_of_leaves` all depend
only on `propext`, `Classical.choice` and `Quot.sound` (VERIFIED, log run 3).

## 6. What remains

- Prove `ProductMetrizationGeo`, `MetrizationExists`, `MetrizationDimUnique` and U. All need
  foundations absent from Mathlib v4.35 (SPECULATIVE sizes):
  - stalks and cotangent spaces of fibre products of schemes (P2a, medium-large);
  - the rank of `ω` for a smooth group scheme (DimUnique, `HodgeLatticeTheorem`; large);
  - the uniformization `A(ℂ) ≅ ℂ^g/Λ` and its uniqueness (Exists, U; very large).
- N1 is a leaf: Néron models are absent from Mathlib.
