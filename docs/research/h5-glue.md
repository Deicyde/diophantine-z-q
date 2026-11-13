# h5-glue: the glue of H5 (Néron models and the stable Faltings height)

Status: research note (task h5-glue, 2026-11-13).
- **Lean:** `scratch/h5-glue/`. Every file imports only `ZInQKernel.HDecomp.Faltings.Leaves` and
  was compiled with `lake env lean`. There is no `sorry` and no `axiom`, and every
  `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`. The main file is
  **`H5Final.lean`** (about 2360 lines, self-contained, compiles in about 18 s).
- **Results log:** `scratch/h5-glue/log.md`.
- **Starting point:** h5-neron (`docs/research/h5-neron.md`, `scratch/h5-neron/`, merged from
  `origin/wip/h5-neron`).
- **Other tasks' material:** hodge-lattice's compiled §1-§5 and §9-§10 are copied verbatim into
  the self-contained files; each copy is marked.
- No file under `ZInQKernel/` or `blueprint/` was edited, and no other task's notes or scratch
  files were edited.

Marks: **VERIFIED** = compiled, or read in Mathlib or the repository. **STANDARD** = published
mathematics with a reference. **SPECULATIVE** = estimate. **UNVERIFIED** = locator from memory
(no network).

## 0. Main result

**`NeronModelMinimal` is a theorem** (VERIFIED):

```lean
theorem ZInQ.H5Glue.neronModelMinimal : ZInQ.DefFaltings.NeronModelMinimal
```

This is the project's own Prop from `Height.lean`: over every number field `L`, a Néron model
has the least height among the smooth group models of `A_L`. The general statement behind it is
also proved:

```lean
theorem ZInQ.H5Glue.heightAntitone : HeightAntitone
-- f : 𝒢.G ⟶ 𝒩.G a homomorphism of group models of A_L, iso on generic fibres ⇒ 𝒩.height ≤ 𝒢.height
```

**H5 in the multi-field form that R19-R21 need now rests on the leaves N1, N2 and two glue
statements instead of six** (VERIFIED, `H5Final.lean`):

```lean
theorem stableFaltingsHeight_eq_neron_all (hN1 : NeronModelExists)
    (hN2 : SemistableNeronIdentityComponent) (hO : OpenImmersionHeightLe)
    (hbc : ModelHeightBaseChange) (K : Type) [Field K] [NumberField K] (A : AbVar K) :
    ∃ L₀ … (𝒩₀ : GroupModel A L₀), 𝒩₀.IsNeronModel ∧ stableFaltingsHeight A = 𝒩₀.height ∧
      ∀ (L' ⊇ L₀) (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel → stableFaltingsHeight A = 𝒩'.height
```

The conclusion matches h5-neron's `stableFaltingsHeight_eq_neron_all` token for token. N1 and
N2 are copied verbatim and kept as hypotheses, as the task asks. The additivity direction
`h(A) + h(B) ≤ h(A × B)` (step E4) now needs only N1 and `ProductModelHeight`
(`stableFaltingsHeight_add_le_of_productModelHeight`).

| h5-neron glue | Status now |
| --- | --- |
| `GroupModelBaseChangeExists` (H4b) | **proved** (`groupModelBaseChangeExists`). h5-neron's attempt hit a kernel timeout |
| `NeronModelMinimal` | **proved** (`neronModelMinimal`, via `heightAntitone`) |
| `OpenSubgroupHeight` (M6) | **reduced** to `OpenImmersionHeightLe` (`openSubgroupHeight_of heightAntitone`). Its clause "an open subgroup model is an isomorphism on generic fibres" is proved (`genericIso_of_openImmersion`) |
| `ModelHeightBaseChange` (H4a) | unchanged (stated, unproved) |
| `ProductGroupModelExists` (P1) | proved by h5-neron |
| `ProductModelHeight` (P2, additivity only) | unchanged |

## 1. Findings

- **(a) `NeronModelMinimal` is glue, and it is now proved.**
  - **The proof.** It needs more than the mapping property: a transport of metrized models along
    the comparison map `f : 𝒢 → 𝒩`. That transport needs four inputs:
    - the local ring at `ξ`;
    - the cotangent map `f^*` and the inclusion `f^*ω_𝒩 ⊆ ω_𝒢`;
    - analytic uniformizations and their Jacobians;
    - `HodgeData.isLattice` for `⋀^g ω_𝒩`.
  - **Where the last input comes from.** Nonvanishing of `⋀^g ω_𝒩` does not follow from
    `f^* : ω_𝒩 ↪ ω_𝒢`. It comes from hodge-lattice's theorem `OmegaSpans` (`ω_𝒩` spans
    `ω_{A_L}`, i.e. coherence of `e*Ω¹`), together with the Hodge line transported from `𝒢`. No
    dimension theory is used (`TangentDimAtOrigin` and `DimBaseChange` are not needed).
  - **Correction.** An earlier draft of this note and the model review (§6) said the proof needs
    the rank half of `HodgeLatticeTheorem`. It does not. h5-neron's finding (d), that
    `NeronModelMinimal` is glue, was right.
- **(b) h5-neron's kernel timeout in H4b came from instance unfolding at concrete types.** The
  fix: prove the monoid-morphism property over abstract morphisms (`a ≫ b = c ≫ d`,
  `c ≫ k = k'`; `genBC_isMonHom`), then instantiate. The file compiles in seconds. The same
  pattern should help other `Over.pullback` glue.
- **(c) Open subgroup models are generic isomorphisms, and no group structure is needed for
  this** (`genericIso_of_openImmersion`):
  - base change keeps the map an open immersion;
  - through `gen` it becomes an open immersion `A_L → A_L` over `L`;
  - that map is universally closed (proper source, separated target), so its image is clopen and
    nonempty in the irreducible `A_L`, hence everything.
- **(d) The archimedean data of `MetrizedModel` depend only on the germ at `ξ`.** Transport along
  a generic isomorphism is formal:
  - complex points go through the adjunction `Over.map ⊣ Over.pullback`;
  - `Spec ℂ → Spec 𝓞_L` hits the generic point, so the unit point lies in every neighbourhood
    of `ξ`;
  - `germ_eq` plus openness of `Φ⁻¹(U(ℂ))` make the germs along `Φ ≫ f` and along `Φ` agree
    near `0`;
  - so the Fréchet derivatives agree (`Filter.EventuallyEq.fderiv_eq`).
- **(e) `GroupModel.height` behaves as intended under generic isomorphisms.** For
  `f : 𝒢 → 𝒩`, `f^*` maps `ω_𝒩` into `ω_𝒢` at every prime, with no hypothesis on `f` beyond
  being a homomorphism (`cotMap_omega`). When `f` is a generic iso, `L ⊗ ⋀^g f^*` is an
  isomorphism of Hodge lines (`hodgeMapBijective`). Pulling the Hodge data back along it can only
  lower the height (`modelHeight_pullHodge_le`, through `secIndex_le_of_map`).

## 2. Lean statements (namespace `ZInQ.H5Glue`; all in `H5Final.lean` unless noted)

| Name | Content | Status |
| --- | --- | --- |
| `genBC_isMonHom`, `GroupModel.baseChange`, `groupModelBaseChangeExists` | H4b: `𝒢 ×_{𝓞_L} 𝓞_{L'}` is a group model of `A_{L'}` | proved |
| `isMonHom_of_map`, `neron_lift_isMonHom` | the Néron comparison map is a homomorphism and a generic iso | proved |
| `isOpenImmersion_pullback_map`, `isIso_of_openImmersion_self`, `genericIso_of_openImmersion` | open immersions of group models are generic isos | proved |
| `ptsEquiv`, `pts_comp_bijective` | a generic iso is bijective on `ℂ`-points | proved |
| `genericFibreStalkIso`, `fst_genericFibreUnit` | copied from hodge-lattice §9-§10 | proved |
| `map_genericUnit`, `stalkIso_of_genericIso` | `f(ξ_𝒢) = ξ_𝒩`; `𝒪_{𝒩,f(ξ)} ≅ 𝒪_{𝒢,ξ}` along a generic iso | proved |
| `evalAt_comp`, `isAnalyticUniformization_comp` | `Φ ↦ Φ ≫ f` transports analytic uniformizations, same period lattice | proved |
| `germAlong_comp_eventuallyEq`, `jacDet_comp_map`, `genMap`, `jacDet_comp_genMap` | Jacobian determinants along `f` and the stalk map `genMap` | proved |
| `genMap_structMap`, `cotMap`, `cotMap_omegaAt`, `cotMap_omega` | `f^* : ω_{𝒩_L} →ₗ[𝓞_L] ω_{𝒢_L}`; `f^*(ω_𝒩) ⊆ ω_𝒢` at every prime | proved |
| `hodgeMap`, `hodgeMap_detLattice`, `hodgeMap_wedgeGerm` | `L ⊗ ⋀^g f^*` maps `⋀^g ω_𝒩` into `⋀^g ω_𝒢` | proved |
| `isIso_genMap`, `cotMap_bijective`, `hodgeMapBijective` | for a generic iso, `L ⊗ ⋀^g f^*` is bijective | proved |
| `secIndex_ne_zero_of_mem`, `secIndex_le_of_map`, `pullHodge`, `modelHeight_pullHodge_le` | pulling Hodge data back along an injective map into the lattice lowers the height | proved |
| `heightAntitone_of`, `hodgeLatticeNonzero_of_omegaSpans`, `heightAntitone_of_omegaSpans` | reductions | proved |
| `omegaSpans`, `heightAntitone`, **`neronModelMinimal`** | final | **proved** |
| `OpenImmersionHeightLe` | open-immersion homomorphism `𝒰 → 𝒢`, generic iso ⇒ `h(𝒰) ≤ h(𝒢)` | **stated** |
| `openSubgroupHeight_of` | `HeightAntitone → OpenImmersionHeightLe → OpenSubgroupHeight` | proved |
| `stableFaltingsHeight_eq_neron_all` | H5, §0 | proved from N1, N2, `OpenImmersionHeightLe`, `ModelHeightBaseChange` |
| `stableFaltingsHeight_add_le_of_productModelHeight` | `h(A)+h(B) ≤ h(C)` for `C ≅ A × B` | proved from N1, P2 |

Copied verbatim from h5-neron (statements, namespace changed): `IsBaseChangeOf`,
`GroupModelBaseChangeExists`, `IsOpenSubgroupModel`, `NeronModelExists` (leaf N1),
`SemistableNeronIdentityComponent` (leaf N2), `ModelHeightBaseChange`, `OpenSubgroupHeight`,
`compositum` (with proof), and the product material (`NeronProp`, `IsProductAbVar`,
`IsProductModel`, `ProductModelHeight`, `productGroupModelExists`,
`stableFaltingsHeight_add_le`).

## 3. Files (all VERIFIED: compiled, 0 errors, standard axioms only)

| File | Content |
| --- | --- |
| **`H5Final.lean`** | everything below combined: `neronModelMinimal`, `heightAntitone`, H4b, open subgroups, the reduction, additivity (8 `#print axioms`) |
| `NeronMinimal.lean` | hodge-lattice §1-§5 (verbatim) + `JacDet.lean` + `Minimal.lean`; `neronModelMinimal` |
| `JacDet.lean` | the transport along a generic isomorphism; `heightAntitone_of_omegaSpans` |
| `H5Glue.lean` | intermediate combined file (H4b, minimality and M6 reductions, H5 from three glue statements) |
| `BaseChange.lean`, `Minimal.lean`, `OpenSub.lean`, `Pts.lean`, `Stalk.lean`, `Analytic.lean`, `Additivity.lean` | the steps, each standalone |

Build: `lake build ZInQKernel.HDecomp.Faltings.Leaves` (1m27 on this host), then
`lake env lean scratch/h5-glue/H5Final.lean` (about 18 s).

## 4. What remains

- **`OpenImmersionHeightLe`.** A metrization of the target `𝒢` must give one of the source `𝒰`
  of no larger height. The machinery of §2 runs in the forward direction, so two pieces are
  missing (SPECULATIVE size: M, about 150 lines):
  - **(i)** `ω_𝒰 ⊆ f^* ω_𝒢`, the converse of `cotMap_omega`. It uses that the stalk maps of an
    open immersion are isomorphisms at every `e_𝒰(s)`. With it, `⋀^g ω_𝒰 = H(⋀^g ω_𝒢)`, and
    `pullHodge` along `H⁻¹` applies.
  - **(ii)** Inverse transport of uniformizations, `Φ_𝒰 = (· ≫ f)⁻¹ ∘ Φ`. It needs
    `dom Φ_𝒰 V = dom Φ (f(V))` (image of an open under an open immersion,
    `preimage_image_eq`), and sections on `V` transported to `f(V)` through
    `IsOpenImmersion.appIso`. The Jacobian then follows from `jacDet_comp_genMap`.
  - No `HodgeLatticeTheorem` input is needed.
- **`ModelHeightBaseChange` (H4a)** is untouched, and it is the largest remaining piece:
  - flat base change of `e*Ω¹`, of `⋀^g` and of the Arakelov degree under `𝓞_L → 𝓞_{L'}`
    (`IdealLines.lean` already has the Arakelov degree of a fractional ideal under base change);
  - restriction of embeddings `τ'|_L`;
  - since `GroupModel.height` is an infimum over metrizations, an exchange of infimum and sum
    over the `τ'` above each `τ`.
- **`ProductModelHeight` (P2)** is untouched.
- **N1, N2** remain literature leaves.

## 5. Recommended decomposition update (for integration after the announcement)

- **Leaves** (unchanged): N1 `NeronModelExists` (BLR §1.4 Thm 3) and N2
  `SemistableNeronIdentityComponent` (SGA 7 IX 3.6 + 3.3). Locators UNVERIFIED.
- **Glue targets:** `OpenImmersionHeightLe`, `ModelHeightBaseChange`, and `ProductModelHeight`
  for additivity.
- **Theorems now:** `NeronModelMinimal`, `GroupModelBaseChangeExists`, `ProductGroupModelExists`.
  `OpenSubgroupHeight` is a corollary of `OpenImmersionHeightLe`.
- **Use in place of h5-neron's versions:**
  - `H5Final.lean`'s `stableFaltingsHeight_eq_neron_all` and
    `stableFaltingsHeight_add_le_of_productModelHeight`;
  - `neronModelMinimal` wherever `NeronModelMinimal` (`Height.lean`) is assumed, e.g. h5-neron's
    `stableFaltingsHeight_add_le`.
- `H5Final.lean` copies hodge-lattice §1-§5. On integration, import it instead of copying.

## 6. Independent review

A read-only model review of `H5Glue.lean` was run (before `heightAntitone` was proved). It checked:
- the truth of `HeightAntitone` and `OpenImmersionHeightLe` for the project's definitions;
- the docstrings;
- that the copied statements match h5-neron token for token;
- that nothing is vacuous (both Props are satisfied by the identity morphism, and neither
  restates its conclusion).

Findings:
- **No false or vacuous statement.**
- **Documentation point:** `HeightAntitone` needs `isLattice` for `⋀^g ω_𝒩`. I then proved
  `HeightAntitone`, and that input comes from `OmegaSpans` (finding (a)). The review's suggestion
  that the rank half of `HodgeLatticeTheorem` is needed is therefore superseded.
- **`OpenImmersionHeightLe`:** true, with no extra input.
- The final proofs (`JacDet.lean`, `NeronMinimal.lean`, `H5Final.lean`) were not reviewed by a
  model. They are Lean proofs of statements that were reviewed. No human review.

## 7. Unchecked

- Locators (BLR, SGA 7, SGA 3) are from memory, as in h5-neron: UNVERIFIED.
- The size estimates in §4 are SPECULATIVE.
- `OpenImmersionHeightLe`, `ModelHeightBaseChange` and `ProductModelHeight` are STANDARD
  mathematics, not Lean proofs.
