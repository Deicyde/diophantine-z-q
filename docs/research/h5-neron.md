# h5-neron: Néron models and the stable Faltings height (node H5, leaves R19-R21)

Status: research note (task h5-neron, 2026-11-12). Lean: `scratch/h5-neron/H5Neron.lean`
(self-contained, imports only `ZInQKernel.HDecomp.Faltings.Leaves`; compiled; no `sorry`, no
`axiom`; every `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`). The parts
also compile separately: `Neron.lean` (A), `ZeroAV.lean` (B), `Reduction.lean` (C). Results log:
`scratch/h5-neron/log.md`. No file under `ZInQKernel/` or `blueprint/` and no other task's files
were edited.

Marks: **VERIFIED** = compiled, or read in a source in the repository or Mathlib. **STANDARD** =
published, with a reference. **SPECULATIVE** = estimate. **UNVERIFIED** = locator from memory (no
network).

## 0. Main result

1. **H5 reduced to two leaves and four glue statements, in Lean** (VERIFIED, compiled).
   `stableFaltingsHeight_eq_neron_all` proves: for every abelian variety `A` over a number field
   `K` there are a finite extension `L₀/K` and a Néron model `𝒩₀/𝓞_{L₀}` with
   `stableFaltingsHeight A = 𝒩₀.height`, and the same equality for the Néron model over **every**
   finite extension `L'/L₀`. Hypotheses:
   - **leaf N1** `NeronModelExists` (Néron; BLR §1.4 Thm 3, UNVERIFIED locator);
   - **leaf N2** `SemistableNeronIdentityComponent` (Grothendieck's semistable reduction,
     SGA 7 IX 3.6, with the base change of the identity component of a semistable Néron model,
     SGA 7 IX 3.3; UNVERIFIED locators);
   - **glue** `NeronModelMinimal` (already in `Height.lean`), `ModelHeightBaseChange`,
     `GroupModelBaseChangeExists`, `OpenSubgroupHeight`;
   - the compositum of two number fields over `K` is **proved** (`compositum`).
2. **The additivity direction `h(A) + h(B) ≤ h(A × B)` (rv-blueprints F1, step E4)** is proved from
   N1, `NeronModelMinimal` and two product glue statements (`stableFaltingsHeight_add_le`). The
   categorical core, "a product of Néron models is a Néron model", is **proved**
   (`NeronProp.tensor`, `isNeronModel_of_isProductModel`). No semistable reduction is needed.
3. **Non-vacuity, in the only case Mathlib can construct** (VERIFIED). For the zero abelian variety
   `AbVar.zero K = Spec K`, the only `AbVar` constructible in Mathlib v4.35:
   - `stableFaltingsHeight (AbVar.zero K) = 0` for every number field `K`
     (`stableFaltingsHeight_zero`); the index set of the infimum is nonempty and the definition
     produces the right value;
   - `StableHeightFinite`, `NeronModelMinimal`, R19, R20 and R21 hold for it, with every
     hypothesis satisfiable (the identity is an isogeny, `x = 0`): `stableHeightFinite_zero`,
     `neronModelMinimal_zero`, `R19_zero`, `R20_zero`, `R21_zero`;
   - the new leaves N1, N2 and the glue hold for it (`neronModelExists_zero`,
     `semistableNeronIdentityComponent_zero`, `glue_zero`).
4. **Not provable now**: `StableHeightFinite` for any nonzero abelian variety, in particular for
   elliptic curves with known models. Mathlib v4.35 cannot construct a nonzero `AbVar` (node AV7:
   no projective group scheme of positive dimension), and it cannot form `A × B` as an `AbVar`
   (VERIFIED: `Mathlib/AlgebraicGeometry/Geometrically/Integral.lean` has base-change instances for
   `GeometricallyIntegral` but no composition instance). Finiteness also needs AN3 and
   `HodgeLatticeTheorem` (def-faltings §3).

## 1. Findings that change the decomposition

- **(a) `LeafAdopt.H5` is not enough for R19-R21.** In h-decomposition, H5 is
  `StableHeightFinite ∧ NeronModelMinimal`. `NeronModelMinimal` compares models **over one field
  `L`**. The published stable height is the Néron height over a field `L₀` of semistable reduction.
  To identify the infimum over all `L` with it, one needs the behaviour under base change: N2,
  `ModelHeightBaseChange` and `OpenSubgroupHeight`. R19 takes the height as an input to an upper
  bound, so a stable height below the published one would make R19 stronger than published. The
  Lean theorem `stableFaltingsHeight_eq_neron_all` is what R19-R21 need. Recommended replacement
  of the leaf H5: the leaves N1, N2, the four glue statements, and `StableHeightFinite`
  (correctness of the definition: needs AN3 and `HodgeLatticeTheorem`).
- **(b) The Néron model does not commute with base change, even in the semistable case.** The
  component group grows under ramified extensions (Tate curve: `Φ ≅ ℤ/ord(q)` grows by the
  ramification index; STANDARD, e.g. Silverman, *Advanced Topics* IV, UNVERIFIED locator). Only
  the identity component commutes with base change (SGA 7 IX 3.3, UNVERIFIED). So
  def-faltings §1 and rv-blueprints §1.3, which cite "the base change of semistable Néron models
  (SGA 7 IX 3.3)", should say "of the identity component". N2 is stated with a common open subgroup
  `𝒰 = 𝒩'⁰ ≅ (𝒩₀⁰)_{L'}`, and the glue `OpenSubgroupHeight` (an open subgroup model has the same
  `ω` and the same complex points, hence the same height) carries the rest.
- **(c) The E4 direction of additivity needs no semistable reduction.** rv-blueprints F1 says
  `h(A) + h(Z) ≤ h(A × Z)` "needs M5 and H5". It needs only N1 (Néron models over each `L`),
  `NeronModelMinimal`, and the product glue: compare over each `L` separately (§3).
- **(d) `NeronModelMinimal` is glue, not a leaf.** It is a statement about the project's
  definition, and it follows from the mapping property (proved here: `IsNeronModel.lift`, the
  comparison map `𝒢 → 𝒩`), the functoriality `ω_𝒩 ⊆ ω_𝒢`, and `HodgeData.modelHeight_le_of_le`
  (in `HodgeData.lean`).

## 2. Statements (Lean names in `ZInQ.H5Neron`)

| Name | Kind | Content | Status |
| --- | --- | --- | --- |
| `NeronProp j P N A e` | def | Néron mapping property along `j : S' → S`, test class `P` | — |
| `GroupModel.isNeronModel_iff` | glue | the project's `IsNeronModel` is `NeronProp` for smooth tests | proved |
| `NeronProp.lift`, `GroupModel.IsNeronModel.lift` | glue | unique extension; the comparison map `𝒢 → 𝒩` | proved |
| `NeronProp.uniqueIso`, `GroupModel.IsNeronModel.uniqueIso` | glue | two Néron models are isomorphic compatibly with `gen` | proved |
| `NeronProp.tensor`, `NeronProp.of_iso`, `isNeronModel_of_isProductModel` | glue | a product of Néron models is a Néron model | proved |
| `IsProductAbVar C A B`, `IsProductModel` | defs | `C ≅ A × B`; `𝒫 ≅ 𝒢₁ × 𝒢₂` compatibly with generic fibres | — |
| `IsBaseChangeOf 𝒢' 𝒢`, `IsOpenSubgroupModel 𝒰 𝒢` | defs | group iso `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}`; open immersion of group schemes | — |
| `NeronModelExists` | **leaf N1** | every `A_L` has a Néron model over `𝓞_L` (BLR §1.4 Thm 3) | stated |
| `SemistableNeronIdentityComponent` | **leaf N2** | ∃ `L₀`, Néron `𝒩₀`; ∀ `L' ⊇ L₀`, ∀ Néron `𝒩'`: a common open subgroup `𝒰` of `𝒩'` and of a base change `𝒱` of `𝒩₀` (SGA 7 IX 3.6 + 3.3) | stated |
| `NeronModelMinimal` | glue (Height.lean) | the Néron model has the least height over each `L` | stated |
| `ModelHeightBaseChange` | glue H4a | `h(𝒢_{L'}) = h(𝒢)` for a fixed smooth model | stated |
| `GroupModelBaseChangeExists` | glue H4b | a group model base-changes to a group model | stated |
| `OpenSubgroupHeight` | glue M6 | an open subgroup model has the same height | stated |
| `ProductGroupModelExists` | glue P1 | group models of `A_L`, `B_L` give one of `C_L` | stated |
| `ProductModelHeight` | glue P2 | `h(𝒢₁) + h(𝒢₂) ≤ h(𝒢₁ × 𝒢₂)` (equality holds) | stated |
| `compositum` | glue | number fields `L, L₀ ⊇ K` embed in a common number field | proved |
| `stableFaltingsHeight_eq_neron(_all)` | H5 | from N1, N2 and the glue (§0.1) | proved |
| `stableFaltingsHeight_add_le` | H7 `≥` | `h(A) + h(B) ≤ h(C)` for `C ≅ A × B` | proved |
| `modelHeight_dim_zero` | glue | every metrized model of dimension `g = 0`, of any `A`, has height `0` | proved |
| `pts_subsingleton`, `no_metrized_succ` | glue | a group model of `Spec K` has one complex point; no metrized model with `g ≥ 1` | proved |
| `trivModel`, `trivModel_isNeronModel`, `metrizedOf` | glue | `Spec 𝓞_L` is a Néron model of `(Spec K)_L`; every group model of it is metrizable | proved |
| `stableFaltingsHeight_zero`, `groupModel_height_zero` | glue | `h(Spec K) = 0`; every group model of `Spec K` has height `0` | proved |
| `R19_zero`, `R20_zero`, `R21_zero`, `stableHeightFinite_zero`, `neronModelMinimal_zero` | instances | the leaves and H5 for the zero abelian variety | proved |
| `neronModelExists_zero`, `semistableNeronIdentityComponent_zero`, `glue_zero` | instances | N1, N2 and the glue for the zero abelian variety | proved |

### Why N1 and N2 are consequences of the publications (STANDARD; locators UNVERIFIED)

- **N1.** For a Dedekind scheme `S` with function field `L`, an abelian variety over `L` has a
  Néron model, a smooth separated `S`-group scheme of finite type with the mapping property for
  all smooth `S`-schemes (BLR 1.2/1, 1.4/3). Each `GroupModel` field holds: finite type implies
  quasi-compact. The group structure comes from the mapping property. The generic fibre is `A_L`
  as a group scheme. Mathlib's `Smooth` is smoothness of every affine-local ring map (finite
  presentation and formal smoothness), i.e. the usual smooth morphism, with no finite-type
  condition (VERIFIED, `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean`). So the test class is
  BLR's.
- **N2.** By SGA 7 IX 3.6 there is a finite `L₀/K` over which `A` has semistable reduction at
  every prime. Let `𝒩₀` be its Néron model. Take `L' ⊇ L₀` and a Néron model `𝒩'` over `𝓞_{L'}`.
  By SGA 7 IX 3.3, applied at each prime after localization (Néron models commute with
  localization and étale base change, BLR 1.2/2), the canonical map `(𝒩₀⁰)_{L'} → 𝒩'⁰` is an
  isomorphism. Then `𝒰 := 𝒩'⁰` (an open subgroup scheme, SGA 3 VI_B 3.10) is a group model of
  `A_{L'}`: open in a smooth separated scheme of finite type, with connected generic fibre `A_{L'}`.
  It is an open subgroup of `𝒩'` and of `𝒱 := 𝒩₀ ×_{𝓞_{L₀}} 𝓞_{L'}`.

### Why the glue is true (STANDARD sketches; to be formalized)

- `ModelHeightBaseChange`: `𝒢` is smooth, so `e*Ω¹` commutes with the flat base change
  `𝓞_L → 𝓞_{L'}`. Hence `⋀^g ω_{𝒢_{L'}} = ⋀^g ω_𝒢 ⊗ 𝓞_{L'}`, and the Arakelov degree is
  multiplied by `[L':L]`. Each `τ' : L' → ℂ` restricts to `τ`, and `𝒢_{L'}(ℂ)_{τ'} = 𝒢(ℂ)_τ`
  with the same uniformization.
- `OpenSubgroupHeight`: an open immersion `𝒰 → 𝒢` of group models is an isomorphism on the local
  rings along the unit section, so the lattices `ω` agree. It is the identity on generic fibres
  (both are `A_L`), so it is the identity on complex points.
- `NeronModelMinimal`: see §1(d).
- `ProductModelHeight`: `ω_{𝒢₁×𝒢₂} = ω₁ ⊕ ω₂`, `det(ω₁ ⊕ ω₂) = det ω₁ ⊗ det ω₂`, and the product
  of uniformizations is a uniformization; this gives equality.
- `GroupModelBaseChangeExists`, `ProductGroupModelExists`: stability of
  smooth/separated/quasi-compact under base change and composition (Mathlib instances), group
  objects through the monoidal functor `Over.pullback`, and the generic fibres by pullback pasting.

## 3. The two derivations (proved; see the Lean file for the full terms)

**H5.** Let `L₀, 𝒩₀` be as in N2. `≤`: `𝒩₀` occurs in the infimum
(`stableFaltingsHeight_eq_iInf_height`, def-faltings). `≥`: take any `L` and `𝒢/𝓞_L`, and let
`L'` be a compositum of `L` and `L₀`. Let `𝒢'` be the base change of `𝒢` to `L'` (H4b), `𝒩'` a
Néron model over `L'` (N1), and `𝒰, 𝒱` as in N2. Then
`h(𝒩₀) = h(𝒱) = h(𝒰) = h(𝒩') ≤ h(𝒢') = h(𝒢)`, by H4a, M6, M6, `NeronModelMinimal` and H4a.

**Additivity.** Fix `L` and a group model `𝒢` of `C_L`. Let `𝒩_A, 𝒩_B` be Néron models over `L`
(N1) and `𝒫` a group model with `𝒫 ≅ 𝒩_A × 𝒩_B` (P1). `𝒫` is a Néron model of `C_L`
(`isNeronModel_of_isProductModel`, proved). So
`h(A) + h(B) ≤ h(𝒩_A) + h(𝒩_B) ≤ h(𝒫) ≤ h(𝒢)`, by the infimum, P2 and `NeronModelMinimal`.
Take the infimum over `L, 𝒢`.

## 4. Dimension 0 (proved)

The facts used for `Spec K`:
- **Hodge line.** `hodgeSpace 0 = L ⊗ ⋀^0 ω ≅ L` (`exteriorPower.zeroEquiv`), and
  `detLattice 0 = 𝓞_L · (1 ⊗ 1)` for every model.
- **Archimedean data.** The coefficient of the empty wedge is `jacDet = det(0×0) = 1`, and the
  covolume of the lattice in `ℂ⁰` is `1`. So every metrized model with `g = 0` has height `0`,
  whatever `A` is (`modelHeight_dim_zero`).
- **No `g ≥ 1` for `Spec K`.** A group model of `Spec K` has exactly one complex point
  (`pts_subsingleton`, via the adjunction `Over.map ⊣ Over.pullback`). The kernel of
  `Φ : ℂ^g → {pt}` is then all of `ℂ^g`, which is not discrete for `g ≥ 1`.
- **Positive dimension.** For `dim A ≥ 1` no `g = 0` metrized model exists, because
  `Φ : ℂ⁰ → A(ℂ)` must be surjective. This is STANDARD and cannot be tested in Lean, since no such
  `A` exists. So the zero-dimensional value `0` is not a normalization artefact: it is the correct
  Faltings height of the zero abelian variety. The theorem is a plumbing test of the definition.
  It is not a test of `g ≥ 1` (rv-blueprints F3).

## 5. What remains

| Item | Size (SPECULATIVE) | Needs |
| --- | --- | --- |
| `GroupModelBaseChangeExists`, `ProductGroupModelExists` | M (category theory) | monoidality of `Over.pullbackComp`, `GrpObj` of products |
| `OpenSubgroupHeight` | M-L | transport of `MetrizedModel` along open immersions (stalks along the unit section, `Pts` bijection) |
| `ModelHeightBaseChange` | L | flat base change of `ω`, `⋀^g` and Arakelov degree under `𝓞_L → 𝓞_{L'}`, restriction of embeddings |
| `NeronModelMinimal` | L | functoriality of `omegaAt` along the comparison map; transport of uniformizations |
| `ProductModelHeight` | L | `⋀` of a direct sum, product uniformizations |
| `StableHeightFinite` (nonzero `A`) | XL | AV7, AN3, `HodgeLatticeTheorem` |
| leaves N1, N2 | literature | Néron models and semistable reduction are absent from Mathlib (prereq-survey) |

Integration suggestion (for after the announcement): replace `LeafAdopt.H5` by N1 and N2 as
leaves, and list the four H5 glue statements, P1 and P2 as glue targets. Keep `StableHeightFinite`
as the correctness-of-definition statement it is (def-faltings §3), and use
`stableFaltingsHeight_eq_neron_all` and `stableFaltingsHeight_add_le` in place of H5 and the
"needs H5" remark in G18.

## 6. Unchecked

- All locators (BLR 1.2/1, 1.2/2, 1.4/3; SGA 7 IX 3.3, 3.6; SGA 3 VI_B 3.10; Silverman) are from
  memory: UNVERIFIED.
- The glue sketches in §2 are STANDARD mathematics, not Lean proofs.
- An independent model review of the Lean statements was run (§7).
