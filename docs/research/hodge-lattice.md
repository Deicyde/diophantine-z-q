# hodge-lattice: the algebraic third of AN3 (`HodgeLatticeTheorem`)

Status: research note (task hodge-lattice, 2026-11-12). Lean: `scratch/hodge-lattice/HodgeLattice.lean`
(about 1190 lines, imports `ZInQKernel.HDecomp.Faltings.Models`, compiled with `lake env lean`,
0 errors, no `sorry`, no `axiom`). Results log: `scratch/hodge-lattice/log.md`. No file under
`ZInQKernel/` or `blueprint/`, and no other task's notes or scratch files, was edited.

Marks: **VERIFIED** = compiled, or read in Mathlib's sources. **STANDARD** = textbook fact.
**SPECULATIVE** = estimate. **UNVERIFIED** = a locator recalled from memory (no network).

## 0. Main result

`ZInQ.DefFaltings.HodgeLatticeTheorem` (ZInQKernel/HDecomp/Faltings/Models.lean) asks, for every
smooth group model `𝒢/𝓞_L` of `A_L` with `A.dim = g`:
- `Module.finrank L (𝒢.hodgeSpace g) = 1`, where `hodgeSpace g = L ⊗_{𝓞_L} ⋀^g_{𝓞_L} (𝔪_ξ/𝔪_ξ²)`;
- `∃ s ∈ 𝒢.detLattice g, s ≠ 0 ∧ secIndex (𝒢.detLattice g) s ≠ 0`, i.e. `⋀^g ω_𝒢` is a full
  lattice in that line.

**It is proved from two standard facts about abelian varieties over a field** (VERIFIED: compiled;
`#print axioms` lists `propext`, `Classical.choice`, `Quot.sound`):

```lean
theorem hodgeLatticeTheorem_of_tangent (h1 : TangentDimAtOrigin) (h3 : DimBaseChange) :
    HodgeLatticeTheorem
```

| Prop (Lean, §8 and §11 of the file) | Statement | Kind |
| --- | --- | --- |
| `TangentDimAtOrigin` | for a field `L`, `B : AbVar L` and `g : ℕ` with `B.dim = g`: `finrank_{κ(0)} (CotangentSpace 𝒪_{B,0}) = g`, where `0 = originPt B` | STANDARD: the tangent space of a smooth variety at a rational point has dimension `dim` |
| `DimBaseChange` | for a field extension `L/K` and `A : AbVar K`: `(A.baseChange L).dim = A.dim` | STANDARD: dimension is invariant under field extension |

`TangentDimAtOrigin` follows in turn from `RegularAtOrigin` (`IsRegularLocalRing 𝒪_{B,0}`) and
`DimAtOrigin` (`ringKrullDim 𝒪_{B,0} = dim B`) (`tangentDimAtOrigin_of`, proved). Both remaining
Props are true (§4). They are stated over Mathlib's genuine objects: `AbVar` is the project's shared
abelian-variety structure over Mathlib schemes, `AbVar.dim` is Mathlib's `topologicalKrullDim`,
`originPt B` is the image of the point of `Spec L` under the unit section, and `CotangentSpace`,
`ResidueField` are Mathlib's. Neither mentions group models, `ω_𝒢`, `⋀^g`, `secIndex` or the
conclusion. What blocks them is exactly the dimension theory of varieties, which Mathlib v4.35 does
not have (§5).

**What is proved in Lean** (everything else):
1. *The algebra* (`hodgeLattice_of_lattice`, §1): for any `𝓞_K`-module `M` and submodule `ω`, if
   `ω` is finitely generated, `rank_K (K ⊗ M) = g`, and `ω` spans `K ⊗ M` over `K`, then
   `K ⊗_{𝓞_K} ⋀^g_{𝓞_K} M` is a `K`-line and the span of the wedges of `ω` is a full lattice in it.
   No base-change theorem for exterior powers is needed (Mathlib has none): the line is spanned by
   one wedge through a determinant identity for alternating maps on `R^g` with values in any module
   (`alt_eq_smulRight`), denominators are cleared through `IsLocalizedModule`, and nonvanishing of
   the wedge is detected by the functional induced by `Basis.det`.
2. *`ω_𝒢` is a finitely generated, full `𝓞_L`-lattice in `ω_{A_L}`* (`omegaLocal`, §5, with the
   local-to-global lemmas of §3-§4). This is the coherence of `e*Ω¹_{𝒢/S}` in the form the
   definition `GroupModel.omega = ⋂_s omegaAt s` needs. It is proved from Mathlib's scheme API:
   affine charts, noetherianity of `Γ(U)`, stalks on affine opens as localizations,
   germ-injectivity on the integral scheme `Spec 𝓞_L`, and a residue lemma. It uses only that
   `𝒢 → Spec 𝓞_L` is locally of finite type and `e` is a section; smoothness is not used here.
3. *The tangent space glue* (§6): `κ(ξ)` is a fraction field of `𝓞_L` (through `structMap`), so
   `rank_L (L ⊗_{𝓞_L} 𝔪_ξ/𝔪_ξ²) = finrank_{κ(ξ)} (𝔪_ξ/𝔪_ξ²)` (`rank_tensor_cotangent`).
4. *Local rings of the generic fibre* (§10, `genericFibreStalkIso`): for every scheme `X` over
   `Spec 𝓞_L`, the projection `X ×_{𝓞_L} Spec L → X` is an isomorphism on all local rings.
5. *The origin* (§9, `originStalkIso_of`): the projection `𝒢_L → 𝒢` sends the identity of `𝒢_L`
   (for the group structure `Functor.grpObjObj` used in `GroupModel.gen_hom`) to `ξ`, and `𝒢.gen`
   sends it to `originPt (A.baseChange L)`. Hence `𝒢.genStalk ≃+* 𝒪_{A_L,0}`, and the cotangent
   dimension transfers (`tangentDim_of_abVar`, through `spanFinrank` of the maximal ideal).
6. *Corollary* (§7, `hodgeLattice_lattice_of_regular`): `ω_𝒢` and `⋀^g ω_𝒢` are finitely generated
   and `L · ⋀^g ω_𝒢 = hodgeSpace g` (the base change of the lattice is the Hodge line). Projectivity
   of the rank-one module `⋀^g ω_𝒢` then follows from the STANDARD fact "finitely generated
   torsion-free over a Dedekind domain is projective". That fact is not formalized: Mathlib v4.35 has
   no lemma in this form (searched `Projective` with `Dedekind`, `torsion`, `FractionalIdeal`:
   nothing).

**Verdict.** The algebraic third of AN3 is formalized down to two textbook facts about varieties over
a field. Both are blocked only by the missing dimension theory of varieties in Mathlib. All the
scheme-theoretic work on the model is done in Lean: coherence of `e*Ω¹`, local rings of the generic
fibre, the identity section, and the residue field.

## 1. Chain of reductions (all arrows proved in Lean)

```
RegularAtOrigin ∧ DimAtOrigin ──tangentDimAtOrigin_of──▶ TangentDimAtOrigin
genericFibreStalkIso : GenericFibreStalkIso (theorem) ──originStalkIso_of──▶ OriginStalkIso
OriginStalkIso ∧ TangentDimAtOrigin ∧ DimBaseChange ──tangentDim_of_abVar──▶ TangentDim
TangentDim ──cotangentRank_of_tangentDim──▶ CotangentRank (rank_L (L ⊗ 𝔪_ξ/𝔪_ξ²) = dim A)
omegaLocal : OmegaLocal (theorem) ──omegaFG_of_omegaLocal, omegaSpans_of_omegaLocal──▶ OmegaFG ∧ OmegaSpans
OmegaFG ∧ CotangentRank ∧ OmegaSpans ──hodgeLatticeTheorem_of──▶ HodgeLatticeTheorem
```

Named intermediate forms:
- `hodgeLatticeTheorem_of_local`: from `OmegaLocal` and `CotangentRank`;
- `hodgeLatticeTheorem_of_cotangentRank`: from `CotangentRank`;
- `hodgeLatticeTheorem_of_regular`: from `RegularOrigin` and `DimOrigin` on `𝒪_{𝒢,ξ}`;
- `hodgeLatticeTheorem_of_abVar`: from `OriginStalkIso`, `RegularAtOrigin`, `DimAtOrigin` and
  `DimBaseChange`;
- `hodgeLatticeTheorem_of_varieties`: the same with `GenericFibreStalkIso` in place of
  `OriginStalkIso`;
- `hodgeLatticeTheorem_of_abVarFacts`: from `RegularAtOrigin`, `DimAtOrigin` and `DimBaseChange`;
- `hodgeLatticeTheorem_of_tangent`: from `TangentDimAtOrigin` and `DimBaseChange`.

## 2. What compiles (VERIFIED)

`lake env lean scratch/hodge-lattice/HodgeLattice.lean` gives 0 errors and 19 warnings
(deprecation of `TensorProduct.induction_on`, style linters, unused-variable linters). Each
`#print axioms` at the end of the file gives `[propext, Classical.choice, Quot.sound]`, for:
`hodgeLattice_of_lattice`, `hodgeLatticeTheorem_of`, `hodgeLatticeTheorem_of_local`, `omegaLocal`,
`hodgeLatticeTheorem_of_cotangentRank`, `hodgeLatticeTheorem_of_regular`,
`hodgeLattice_lattice_of_regular`, `hodgeLatticeTheorem_of_abVar`, `originStalkIso_of`,
`hodgeLatticeTheorem_of_varieties`, `genericFibreStalkIso`, `hodgeLatticeTheorem_of_abVarFacts`,
`hodgeLatticeTheorem_of_tangent`. The file needs `lake build ZInQKernel.HDecomp.Faltings.Models`
first (1m51 on this host). The identity `𝒢.detLattice g = detLat 𝒢.omega g` holds by `rfl`
(`detLattice_eq`), so the generic algebra applies to the definitions of Models.lean verbatim.

## 3. The proofs in outline

### 3.1 Algebra (§1)

Let `V = K ⊗ M`, and let `b` be a `K`-basis of `V` of the form `1 ⊗ w_j` with `w_j ∈ ω` (it exists
since `ω` spans and `rank V = g`). Then:
- (`exists_clear`) every `v ∈ M` has `D • v = Σ a_j w_j` in `M` for some `0 ≠ D ∈ 𝓞_K`. Write
  `1 ⊗ v` in the basis and clear denominators. `M → K ⊗ M` is a localization map
  (`isLocalizedModule_iff_isBaseChange` with `TensorProduct.isBaseChange`), so an element killed
  in `K ⊗ M` is killed by a nonzero scalar.
- (`tmul_ιMulti_mem_span`) `(∏ D_i) • ιMulti v = ιMulti(ψ ∘ a) = det(a) • ιMulti w`, where
  `ψ : 𝓞_K^g → M` sends `e_j ↦ w_j`. The second equality is `alt_eq_smulRight` (an alternating map
  on `R^g` with values in any module is `det · F(e)`, from `Basis.ext_alternating`). Hence every
  `1 ⊗ ιMulti v` lies in `K · s₀`, where `s₀ = 1 ⊗ ιMulti w`, and `K · s₀ = K ⊗ ⋀^g M`.
- `s₀ ≠ 0`: the `𝓞_K`-alternating map `v ↦ det_b(1 ⊗ v)` induces
  `Ψ : K ⊗ ⋀^g M → K` (`exteriorPower.alternatingMapLinearEquiv`, `LinearMap.liftBaseChange`)
  with `Ψ s₀ = det_b b = 1`.
- Finite index: `detLat ω g` lies in the image of `⋀^g ω`, which is finitely generated (Mathlib's
  `exteriorPower.instFinite`). Hence it lies in `𝓞_K · t₀` with `s₀ = d • t₀`, and
  `[𝓞_K t₀ : 𝓞_K s₀] = |N(d)|` (`secIndex_smul` of HodgeData.lean).

### 3.2 `ω_𝒢` is a lattice (§3-§5)

`OmegaLocal` says: near every `s ∈ Spec 𝓞_L` there are `a ∉ s` and a finitely generated
`N ⊆ ω_{A_L}` spanning over `L`, with `N ≤ omegaAt s'` and `omegaAt s' ⊆ N_{s'}` for all
`s' ∈ D(a)`.

Proof (`omegaLocal`). Take an affine open `U ∋ e(s)` (`isBasis_affineOpens`) and `D(a) ⊆ e⁻¹U`.
`Γ(U)` is noetherian (`LocallyOfFiniteType.isLocallyNoetherian`, `component_noetherian`), so
`I = ker(e^* : Γ(U) → Γ(e⁻¹U))` has finitely many generators `i_k`. Put `N = 𝓞_L-span{d i_k}`.
- `N ≤ omegaAt s'`: the germ of `i_k` at `e(s')` lies in the kernel of the stalk map
  (`dCls_mem_omegaAt`).
- `omegaAt s' ⊆ N_{s'}`: a germ `f` in the kernel at `e(s')` is `b/u` with `b, u ∈ Γ(U)`
  (`IsAffineOpen.isLocalization_stalk`). Then `e^* b` has zero germ at `s'`, so `e^* b = 0`
  (`germ_injective_of_isIntegral`), so `b ∈ I = Σ Γ(U) i_k`. The coefficients become
  `𝓞_L`-fractions with denominators outside `s'` by the **residue lemma** (`residue`): every germ at
  `e(s')`, specialized to `ξ`, is `≡ c/t mod 𝔪_ξ` with `t ∉ s'`. Its proof uses that the stalk of
  `Spec 𝓞_L` at `s'` is a localization, `e ≫ π = 𝟙`, and `Scheme.Hom.stalkSpecializes_stalkMap`.
- `N` spans: apply the previous item at the generic point, where `omegaAt = ⊤` (`omegaAt_genericPt`
  of Models.lean).

Local-to-global (`fg_iInf_of_local`, `exists_smul_mem_iInf_of_local`): finitely many `D(a)` cover
`Spec 𝓞_L` (`Ideal.span_eq_top_iff_finite`), and `x ∈ N₀_m` for all maximal `m` implies `x ∈ N₀`.

### 3.3 Tangent space (§6)

`isUnit_structMap`: `c ≠ 0 ⇒ structMap c` is a unit of `𝒪_{𝒢,ξ}`, because its image in the
function field of `Spec 𝓞_L` is nonzero and stalk maps are local. With the residue lemma at the
generic point this makes `κ(ξ)` a fraction field of `𝓞_L`. Then `L ≃ₐ[𝓞_L] κ(ξ)`
(`IsLocalization.algEquiv`) makes `𝔪_ξ/𝔪_ξ²` an `L`-module, `isLocalizedModule_id` gives
`IsBaseChange L id`, and `rank_eq_of_equiv_equiv` compares ranks over `L` and `κ(ξ)`.

### 3.4 The origin and the generic fibre (§9-§11)

- The identity `η` of the generic fibre is `ε ≫ (Over.pullback f).map η_𝒢` (`Functor.monObjObj`).
  So `η_{𝒢_L}.left ≫ pullback.fst = f ≫ e`, from `pullback.condition` and `Over.w ε`
  (`fst_genericFibre_unit`), and `f` sends the point of `Spec L` to the generic point
  (`toGeneric_pt`). `IsMonHom.one_hom` for `𝒢.gen.hom` gives `gen(ξ_L) = originPt`. A scheme
  isomorphism is an open immersion, hence an isomorphism on stalks
  (`IsOpenImmersion.iff_isIso_stalkMap`); `stalkCongr` moves between equal points.
- `genericFibreStalkIso`: "all stalk maps bijective" (`stalkwise`) respects isomorphisms and is
  Zariski-local on the target (`stalkwiseIsZariskiLocalAtTarget_of_respectsIso`). Over an affine
  chart `Spec A → X` (`affineOpenCover`), the pullback is identified with
  `Spec (A ⊗_{𝓞_L} L) → Spec A` by `pullbackSymmetry`, `pullbackRightPullbackFstIso`,
  `pullback.congrHom` (with `Spec.map_preimage`) and `pullbackSpecIso`. `A ⊗_{𝓞_L} L` is the
  localization of `A` at the image of `𝓞_L ∖ 0` (`IsLocalization.tensor`), and Mathlib's
  `isIso_specMap_stalkMap_localization` finishes (`stalkwise_tensor_localization`).
- `tangentDim_of_abVar`: `finrank_{κ} CotangentSpace = spanFinrank 𝔪` for noetherian local rings
  (`spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`), and `spanFinrank` is invariant under ring
  isomorphisms (`Ideal.spanFinrank_map_eq_of_ringEquiv`, `map_ringEquiv_maximalIdeal`).

## 4. The remaining statements: truth and references

Both are true for the definitions as they stand (STANDARD; locators UNVERIFIED):
- `TangentDimAtOrigin`. `B` is smooth and geometrically integral over `L`, of dimension `g`, and
  `0` is an `L`-rational (closed) point. Two routes:
  - the local ring of a smooth variety is regular (`RegularAtOrigin`; EGA IV 17.5.1, UNVERIFIED),
    and the local ring of an irreducible variety at a closed point has dimension `dim`
    (`DimAtOrigin`; Hartshorne I.1.8A and II Ex. 3.20, UNVERIFIED);
  - or: `Ω¹_{B/L}` is locally free of rank `dim B`, and `𝔪/𝔪² ≅ Ω¹ ⊗ κ(0)` at a rational point.
- `DimBaseChange`. For a scheme of finite type over a field, `dim X_L = dim X` (EGA IV 4.1.4 /
  Stacks "dimension of fibres under field extension", UNVERIFIED). The project's
  `AbVar.baseChange` is the genuine fibre product (`Over.pullback`, Objects.lean).

Sanity check: for the zero abelian variety `Spec K` (the only one Mathlib can construct, per
Objects.lean), the local ring at the origin is the field `K`, with cotangent space `0` and dimension
`0`, so both Props hold. The project's `AbVar.dim` is `topologicalKrullDim A.X.left : WithBot ℕ∞`,
and `A.dim = g` is the coercion of `g : ℕ`; the Props use the same convention as
`HodgeLatticeTheorem`.

## 5. What Mathlib v4.35 lacks (precisely)

Searched in `.lake/packages/mathlib` (VERIFIED by grep; absence claims are about these searches):
1. **Dimension theory of varieties.**
   - Missing: a lemma computing `ringKrullDim` of a local ring of a finitely generated algebra over
     a field at a maximal ideal, or `topologicalKrullDim` of a scheme of finite type over a field;
     invariance of `ringKrullDim` under integral extensions (going up/down to dimension); "every
     maximal ideal of an affine domain has height `dim`".
   - Present: `MvPolynomial.ringKrullDim_of_isNoetherianRing` (dimension of polynomial rings),
     Noether normalization (`exists_finite_inj_algHom_of_fg`), Krull's height theorem.
   - Blocks `DimAtOrigin`.
2. **Dimension under field extension.** No lemma relating `topologicalKrullDim` of `X ×_K L` and of
   `X`. Blocks `DimBaseChange`.
3. **Smooth ⇒ regular.**
   - Present: `IsRegularLocalRing` (`RingTheory/RegularLocalRing/Defs.lean`, with
     `iff_finrank_cotangentSpace`) and `RegularLocalRing/Polynomial.lean` (localizations of
     polynomial rings).
   - Missing: no file under `RingTheory/Smooth` or `RingTheory/Etale` mentions `IsRegularLocalRing`
     or `ringKrullDim`.
   - Blocks `RegularAtOrigin`. A route: étale-locally `B` is `𝔸^g_L`, plus "étale preserves
     regularity and dimension"; both are missing.
4. Not missing after all: stalks of a base change along `Spec L → Spec 𝓞_L`. `genericFibreStalkIso`
   proves this here from existing Mathlib lemmas.

Mathlib lemmas used:
- stalks and opens: `IsAffineOpen.isLocalization_stalk`, `germ_injective_of_isIntegral`,
  `Scheme.Hom.germ_stalkMap_apply`, `Scheme.Hom.stalkSpecializes_stalkMap_apply`,
  `isBasis_affineOpens`, `basicOpen_eq_of_affine`;
- noetherianity: `LocallyOfFiniteType.isLocallyNoetherian`,
  `IsLocallyNoetherian.component_noetherian`;
- cotangent spaces: `Ideal.Cotangent.smul_eq_zero_of_mem`,
  `IsRegularLocalRing.iff_finrank_cotangentSpace`,
  `spanFinrank_maximalIdeal_eq_finrank_cotangentSpace`;
- exterior powers: `exteriorPower.ιMulti_span`, `exteriorPower.alternatingMapLinearEquiv`,
  `exteriorPower.instFinite`, `Basis.ext_alternating`;
- localization and rank: `isLocalizedModule_iff_isBaseChange`, `isLocalizedModule_id`,
  `rank_eq_of_equiv_equiv`;
- the generic fibre: `stalkwiseIsZariskiLocalAtTarget_of_respectsIso`, `pullbackSpecIso`,
  `IsLocalization.tensor`, `isIso_specMap_stalkMap_localization`.

## 6. Integration notes

- The file imports only `ZInQKernel.HDecomp.Faltings.Models`. As a build module it would go next to
  it (e.g. `ZInQKernel/HDecomp/Faltings/HodgeLatticeProof.lean`). It does not touch the upstream
  contract: `HodgeLatticeTheorem` is HDecomp glue, not one of the five registered hypotheses.
- In h-decomposition.md, `HodgeLatticeTheorem` can be replaced by `TangentDimAtOrigin` and
  `DimBaseChange` (or by the three Props `RegularAtOrigin`, `DimAtOrigin`, `DimBaseChange`). These
  are textbook facts about varieties over a field rather than refereed literature theorems. They can
  be crowdsourced independently of the model theory.
- `HodgeLatticeTheorem` makes R19-R21 non-vacuous only together with AN3's analytic Props
  (`AnalyticUniformizationExists`, `AnalyticUniformizationUnique`), which this task did not touch.

## 7. Unchecked items

- All textbook locators in §4 are from memory (UNVERIFIED).
- Projectivity and invertibility of `⋀^g ω_𝒢` (the "projective of rank one" phrasing of the task)
  are STANDARD consequences of the corollary in §7 of the file, not proved in Lean.
  `HodgeLatticeTheorem` as stated does not ask for them.
- No independent (model) review of the new Props was run.
