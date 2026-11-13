# h5-glue: the glue of H5 (Néron models and the stable Faltings height)

Status: research note (task h5-glue, 2026-11-13). Lean: `scratch/h5-glue/` (seven self-contained
files, each importing only `ZInQKernel.HDecomp.Faltings.Leaves`; each compiled with
`lake env lean`; no `sorry`, no `axiom`; every `#print axioms` lists only `propext`,
`Classical.choice`, `Quot.sound`). Results log: `scratch/h5-glue/log.md`. Starting point:
h5-neron (`docs/research/h5-neron.md`, `scratch/h5-neron/`, merged from `origin/wip/h5-neron`).
No file under `ZInQKernel/` or `blueprint/` was edited, and no other task's notes or scratch
files were edited.

Marks: **VERIFIED** = compiled, or read in Mathlib or the repository. **STANDARD** = published
mathematics with a reference. **SPECULATIVE** = estimate. **UNVERIFIED** = locator from memory
(no network).

## 0. Main result

**H5 in the multi-field form that R19-R21 need now rests on the leaves N1, N2 and three glue
statements instead of six** (VERIFIED, `scratch/h5-glue/H5Glue.lean`):

```lean
theorem stableFaltingsHeight_eq_neron_all (hN1 : NeronModelExists)
    (hN2 : SemistableNeronIdentityComponent) (hA : HeightAntitone) (hO : OpenImmersionHeightLe)
    (hbc : ModelHeightBaseChange) (K : Type) [Field K] [NumberField K] (A : AbVar K) :
    ∃ L₀ … (𝒩₀ : GroupModel A L₀), 𝒩₀.IsNeronModel ∧ stableFaltingsHeight A = 𝒩₀.height ∧
      ∀ (L' ⊇ L₀) (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel → stableFaltingsHeight A = 𝒩'.height
```

The conclusion is h5-neron's `stableFaltingsHeight_eq_neron_all` token for token. N1 and N2 are
copied verbatim and kept as hypotheses, as the task asks. The glue of h5-neron's version now
stands as follows:

| h5-neron glue | Status now | Where |
| --- | --- | --- |
| `GroupModelBaseChangeExists` (H4b) | **proved** (`groupModelBaseChangeExists`; h5-neron's attempt hit a kernel timeout) | `BaseChange.lean`, `H5Glue.lean` §1 |
| `NeronModelMinimal` | **reduced** to `HeightAntitone` (`neronModelMinimal_of_heightAntitone`). The Néron comparison map is proved to be a group homomorphism and an isomorphism on generic fibres | `Minimal.lean`, `H5Glue.lean` §2 |
| `OpenSubgroupHeight` (M6) | **reduced** to `HeightAntitone` + `OpenImmersionHeightLe` (`openSubgroupHeight_of`). Its clause "an open subgroup model is an isomorphism on generic fibres" is **proved** (`genericIso_of_openImmersion`) | `OpenSub.lean`, `H5Glue.lean` §3, §5 |
| `ModelHeightBaseChange` (H4a) | unchanged (stated, unproved) | copied |
| `ProductModelHeight` (P2, additivity only) | unchanged. Additivity now needs only N1, `HeightAntitone` and P2 (`stableFaltingsHeight_add_le_of_heightAntitone`) | `Additivity.lean` |

**Most of `HeightAntitone` is proved** (VERIFIED, `Stalk.lean`, `JacDet.lean`). Let
`f : 𝒢 → 𝒩` be a homomorphism of group models that is an isomorphism on generic fibres.
- It induces an isomorphism of local rings at the identity `ξ` of the generic fibre
  (`stalkIso_of_genericIso`).
- It sends `ξ_𝒢` to `ξ_𝒩` (`map_genericUnit`).
- It induces bijections on complex points (`pts_comp_bijective`).
- It transports analytic uniformizations (`isAnalyticUniformization_comp`) and their Jacobian
  determinants (`jacDet_comp_genMap`).
- It induces an `𝓞_L`-linear map `f^*` on cotangent spaces at `ξ` (`cotMap`).

What is still missing is the algebraic Hodge-lattice transport (§4).

## 1. Findings

- **(a) `NeronModelMinimal` is not pure glue over the mapping property.** This corrects
  h5-neron finding (d). To bound `h(𝒩)` you must build a metrization of the Néron model 𝒩 from
  one of `𝒢`, and that needs `HodgeData.isLattice` for `𝒩.detLattice g`: a nonzero element of
  finite index.
  - Finite index does follow from `𝒢`. `f^*` maps `⋀^g ω_𝒩` into `⋀^g ω_𝒢`, and a nonzero
    `𝓞_L`-submodule of a rank-one lattice has finite index.
  - Nonvanishing does not follow. It says that `ω_𝒩` has full generic rank, and `f^*` only gives
    `ω_𝒩 ↪ ω_𝒢`.
  - So the proof of `HeightAntitone`, and hence of `NeronModelMinimal`, needs the full-rank half
    of `HodgeLatticeTheorem` for 𝒩. That theorem is true (𝒩 is smooth) and is stated in
    `Models.lean`. hodge-lattice reduced it to `TangentDimAtOrigin` and `DimBaseChange`.
  - Found independently by me and by the model review (§6). `HeightAntitone` itself is true:
    the statement is right, only its proof has this dependency.
- **(b) h5-neron's kernel timeout in H4b came from instance unfolding at concrete types.**
  Proving the monoid-morphism property of the generic-fibre identification over *abstract*
  morphisms `a ≫ b = c ≫ d`, `c ≫ k = k'` (`genBC_isMonHom`) and only then instantiating with
  `Spec.map (algebraMap (𝓞 L) L)` etc. compiles in seconds. The concrete version made the kernel
  unfold those terms. This pattern should help other `Over.pullback` glue (VERIFIED).
- **(c) Open subgroup models are generic isomorphisms, and no group structure is needed.**
  `genericIso_of_openImmersion` holds for any morphism of group models whose underlying map is an
  open immersion:
  - base change keeps it an open immersion;
  - through `gen` it becomes an open immersion `A_L → A_L` over `L`;
  - that map is universally closed (proper source, separated target), so its image is clopen and
    nonempty in the irreducible `A_L`.
  - Mathlib supplies: `GeometricallyIrreducible.irreducibleSpace_of_subsingleton`,
    `UniversallyClosed.of_comp_of_isSeparated`, `isIso_iff_isOpenImmersion_and_surjective`.
- **(d) The archimedean side of the height comparison is formal.** Transport along a generic
  isomorphism needs four things: the adjunction `Over.map ⊣ Over.pullback` for points; the fact
  that `Spec ℂ → Spec 𝓞_L` hits the generic point, so the unit point lies in every neighbourhood
  of `ξ`; `germ_eq` with openness of `Φ⁻¹(U(ℂ))`, which makes germs along `Φ ≫ f` and along `Φ`
  agree near `0`; and `Filter.EventuallyEq.fderiv_eq`. So the archimedean data of
  `MetrizedModel` depend only on the germ at `ξ`, as intended.

## 2. Statements (namespace `ZInQ.H5Glue`)

| Name | Kind | Content | Status |
| --- | --- | --- | --- |
| `genBC`, `genBC_isMonHom` | glue | generic-fibre identification of a base change, for abstract morphisms; it is a monoid morphism | proved |
| `GroupModel.baseChange L L' 𝒢` | def | `𝒢 ×_{𝓞_L} 𝓞_{L'}` as a `GroupModel A L'` | — |
| `groupModelBaseChangeExists` | glue H4b | `GroupModelBaseChangeExists` (h5-neron's statement) | **proved** |
| `isMonHom_of_map` | glue | a strong monoidal functor injective on `Hom(𝟙,Y)`, `Hom(X⊗X,Y)` reflects monoid morphisms | proved |
| `neron_lift`, `neron_map_injective`, `neron_lift_isMonHom` | glue | the comparison map `𝒢 → 𝒩` to a Néron model is a homomorphism and a generic isomorphism | proved |
| `HeightAntitone` | **glue, stated** | `f : 𝒢 → 𝒩` homomorphism, `F(f)` iso ⇒ `h(𝒩) ≤ h(𝒢)` | open (§4) |
| `neronModelMinimal_of_heightAntitone` | reduction | `HeightAntitone → NeronModelMinimal` | proved |
| `isOpenImmersion_pullback_map` | glue | `Over.pullback` preserves open immersions | proved |
| `isIso_of_openImmersion_self` | glue | an open immersion `B → B` over `Spec L` of an abelian variety is an isomorphism | proved |
| `genericIso_of_openImmersion` | glue | an open immersion of group models is an isomorphism on generic fibres | proved |
| `OpenImmersionHeightLe` | **glue, stated** | open-immersion homomorphism `𝒰 → 𝒢`, generic iso ⇒ `h(𝒰) ≤ h(𝒢)` | open |
| `openSubgroupHeight_of` | reduction | `HeightAntitone → OpenImmersionHeightLe → OpenSubgroupHeight` | proved |
| `stableFaltingsHeight_eq_neron_all` | H5 | §0 | proved |
| `stableFaltingsHeight_add_le_of_heightAntitone` | H7 `≥` | `h(A)+h(B) ≤ h(C)` from N1, `HeightAntitone`, P2 | proved |
| `ptsEquiv`, `pts_comp_bijective` | glue | `𝒢(ℂ)_τ ≃` points of the generic fibre; a generic iso is bijective on `ℂ`-points | proved |
| `genericFibreStalkIso`, `fst_genericFibreUnit` | glue | copied verbatim from hodge-lattice §9-§10 | proved (there and here) |
| `map_genericUnit`, `stalkIso_of_genericIso` | glue | `f(ξ_𝒢) = ξ_𝒩`; `f` induces an iso `𝒪_{𝒩,f(ξ)} → 𝒪_{𝒢,ξ}` | proved |
| `evalAt_comp`, `dom_comp`, `isAnalyticUniformization_comp` | glue | values along `f`; `Φ ↦ Φ ≫ f` transports analytic uniformizations, same period lattice | proved |
| `evalAt_res`, `ptC_hom_apply`, `one_mem_dom`, `germAlong_comp_eventuallyEq`, `jacDet_comp_map` | glue | germ comparison near `0`; Jacobian determinants along `f` | proved |
| `genMap`, `genMap_germ`, `jacDet_comp_genMap` | glue | the stalk comparison `𝒪_{𝒩,ξ} → 𝒪_{𝒢,ξ}`; `jacDet (Φ≫f) t = jacDet Φ (genMap ∘ t)` | proved |
| `genMap_mem_maximalIdeal`, `genMap_structMap`, `cotMap`, `cotMap_dCls` | glue | `genMap` is local and `𝓞_L`-compatible; `f^* : ω_{𝒩_L} →ₗ[𝓞_L] ω_{𝒢_L}` with `f^* (dt) = d(genMap t)` | proved |

Copied verbatim from h5-neron (statements; namespace changed): `IsBaseChangeOf`,
`GroupModelBaseChangeExists`, `IsOpenSubgroupModel`, `NeronModelExists` (leaf N1),
`SemistableNeronIdentityComponent` (leaf N2), `ModelHeightBaseChange`, `OpenSubgroupHeight`,
`compositum` (with proof). `Additivity.lean` also copies h5-neron's product material
(`NeronProp`, `IsProductAbVar`, `IsProductModel`, `ProductModelHeight`,
`productGroupModelExists`, `stableFaltingsHeight_add_le`).

## 3. Files (all VERIFIED: compiled, 0 errors, standard axioms only)

| File | Content | `#print axioms` |
| --- | --- | --- |
| `BaseChange.lean` | H4b | 2 |
| `Minimal.lean` | Néron comparison map; `NeronModelMinimal ⇐ HeightAntitone` | 3 |
| `OpenSub.lean` | open immersions are generic isos | 3 |
| `Pts.lean` | points along generic isos | 1 |
| `H5Glue.lean` | combined: the four files above plus §5 (reduction, `stableFaltingsHeight_eq_neron_all`) | 12 |
| `Additivity.lean` | `stableFaltingsHeight_add_le_of_heightAntitone` | 2 |
| `Stalk.lean` | local ring at `ξ` along a generic iso (with hodge-lattice's lemmas) | 3 |
| `JacDet.lean` | `Pts.lean` + archimedean transport + `genMap` + `cotMap` | 9 |

Build: `lake build ZInQKernel.HDecomp.Faltings.Leaves` (1m27 here), then
`lake env lean scratch/h5-glue/<file>.lean`. Each file takes 5-25 s.

## 4. What remains (to prove `HeightAntitone` and `OpenImmersionHeightLe`)

The remaining steps for `HeightAntitone`, given `M : MetrizedModel A L g` with `M.model = 𝒢`:

| Step | Content | Size (SPECULATIVE) |
| --- | --- | --- |
| R1 | `cotMap` sends `ω_𝒩 = ⋂_s omegaAt_𝒩 s` into `ω_𝒢`. At each `s`: `f(e_𝒢(s)) = e_𝒩(s)`; `f^*` maps `ker(𝒪_{𝒩,e(s)} → 𝒪_{S,s})` into the kernel for `𝒢` (`stalkMap_comp` along `e_𝒢 ≫ f = e_𝒩`); and it commutes with specialization to `ξ` (`stalkSpecializes_stalkMap`) | M (dependent-type rewriting along point equalities) |
| R2 | `L ⊗ ⋀^g cotMap` is an `L`-linear isomorphism `𝒩.hodgeSpace g ≃ 𝒢.hodgeSpace g` (`cotMap` is bijective because `genMap` is an isomorphism, by `stalkIso_of_genericIso`) and maps `detLattice_𝒩` into `detLattice_𝒢` (by R1) | M |
| R3 | `detLattice_𝒩 ≠ 0`, from the full-rank half of `HodgeLatticeTheorem` for 𝒩 (finding (a)); then finite `secIndex` from R2 | S given `HodgeLatticeTheorem` |
| R4 | transport of `HodgeData` along an `L`- and `𝓞_L`-linear isomorphism, with `modelHeight` preserved; then `HodgeData.modelHeight_le_of_le`, with coefficient `coeff_𝒢 ∘ (L ⊗ ⋀^g cotMap)` (agreeing on wedges by `jacDet_comp_genMap` and `semilinear_ext_wedge`) and the same period lattices (`isAnalyticUniformization_comp`) | M |

So `HeightAntitone` would follow from `HodgeLatticeTheorem` (or only its rank half for the
target model) plus R1, R2 and R4. Those three are algebra over objects that are already defined.

`OpenImmersionHeightLe` runs in the other direction: a metrization of the target `𝒢` gives one
of the source `𝒰`.
- It needs the inverse transport of uniformizations: `Φ_𝒰 = (· ≫ f)⁻¹ ∘ Φ_𝒢`. Openness of the
  domains uses the image of opens under the open immersion.
- It needs `ω_𝒰 = f^* ω_𝒢`: the stalk maps of an open immersion are isomorphisms at every
  `e_𝒰(s)`.
- No `HodgeLatticeTheorem` is needed, because the lattices are equal (model review, §6).
- The review notes that an `OpenImmersionHeightEq` would be the more natural statement. The
  total dependencies are the same.

`ModelHeightBaseChange` (H4a) is untouched. It is the largest piece: flat base change of
`e*Ω¹`, of `⋀^g` and of the Arakelov degree under `𝓞_L → 𝓞_{L'}`, and the restriction of
embeddings `τ'|_L`. Since `GroupModel.height` is an infimum over metrizations, it also needs an
exchange of infimum and sum over the `τ'` above each `τ`. `ProductModelHeight` (P2) is untouched.

## 5. Recommended decomposition update (for integration after the announcement)

- **Leaves** (unchanged): N1 `NeronModelExists` (BLR §1.4 Thm 3), N2
  `SemistableNeronIdentityComponent` (SGA 7 IX 3.6 + 3.3); locators UNVERIFIED.
- **Glue targets:** `HeightAntitone` (whose proof uses `HodgeLatticeTheorem`),
  `OpenImmersionHeightLe`, `ModelHeightBaseChange`, and `ProductModelHeight` for additivity.
  `GroupModelBaseChangeExists` and `ProductGroupModelExists` are theorems.
  `NeronModelMinimal` and `OpenSubgroupHeight` are corollaries.
- Use `stableFaltingsHeight_eq_neron_all` from `H5Glue.lean` in place of h5-neron's version,
  and `stableFaltingsHeight_add_le_of_heightAntitone` for the E4 direction.

## 6. Independent review

A read-only model review of `H5Glue.lean` checked several things:
- the truth of `HeightAntitone` and `OpenImmersionHeightLe` for the project's definitions;
- the accuracy of the docstrings;
- that the copied statements match h5-neron token for token;
- that nothing is vacuous: both Props are satisfied by the identity morphism, and neither
  restates its conclusion.

Findings:
- **No problem.** No statement is false or vacuous.
- **One documentation point:** the `isLattice` dependency of `HeightAntitone` (finding (a)). It
  is now recorded in the docstring of `HeightAntitone` in `Minimal.lean`, `H5Glue.lean` and
  `Additivity.lean` (all recompiled), here, and in the log.
- **Minor:** the header's "copied verbatim" applies to the statements; some docstrings are
  shortened.

No human review.

## 7. Unchecked

- Locators (BLR, SGA 7, SGA 3) are from memory, as in h5-neron: UNVERIFIED.
- The size estimates in §4 are SPECULATIVE.
- `HeightAntitone`, `OpenImmersionHeightLe` and `ModelHeightBaseChange` are STANDARD
  mathematics (see h5-neron §2 and §4 above), not Lean proofs.
