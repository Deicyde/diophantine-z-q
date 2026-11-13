# hodge-lattice: the algebraic third of AN3 (`HodgeLatticeTheorem`)

Status: research note (task hodge-lattice, 2026-11-12). Lean: `scratch/hodge-lattice/HodgeLattice.lean`
(imports `ZInQKernel.HDecomp.Faltings.Models`, compiled with `lake env lean`, 0 errors, no `sorry`,
no `axiom`). Results log: `scratch/hodge-lattice/log.md`. No file under `ZInQKernel/` or
`blueprint/`, and no other task's notes or scratch files, was edited.

Marks: **VERIFIED** = compiled, or read in Mathlib's sources. **STANDARD** = textbook fact.
**SPECULATIVE** = estimate. **UNVERIFIED** = a locator recalled from memory (no network).

## 0. Main result

`ZInQ.DefFaltings.HodgeLatticeTheorem` (ZInQKernel/HDecomp/Faltings/Models.lean) asks, for every
smooth group model `𝒢/𝓞_L` of `A_L` with `A.dim = g`:
- `Module.finrank L (𝒢.hodgeSpace g) = 1`, where `hodgeSpace g = L ⊗_{𝓞_L} ⋀^g_{𝓞_L} (𝔪_ξ/𝔪_ξ²)`;
- `∃ s ∈ 𝒢.detLattice g, s ≠ 0 ∧ secIndex (𝒢.detLattice g) s ≠ 0`, i.e. `⋀^g ω_𝒢` is a full
  lattice in that line.

**It is now proved from four statements, none about models or Hodge lattices** (VERIFIED: compiled;
`#print axioms` lists `propext`, `Classical.choice`, `Quot.sound`):

```lean
theorem hodgeLatticeTheorem_of_abVar (h0 : OriginStalkIso) (h1 : RegularAtOrigin)
    (h2 : DimAtOrigin) (h3 : DimBaseChange) : HodgeLatticeTheorem
```

| Prop | Statement (Lean, `scratch/hodge-lattice/HodgeLattice.lean` §8) | Kind |
| --- | --- | --- |
| `OriginStalkIso` | `𝒢.genStalk ≃+* 𝒪_{A_L, 0}`: the local ring of `𝒢` at the identity `ξ` of its generic fibre is the local ring of `A_L` at its origin (`originPt`) | scheme theory (stalks of a base change along the localization `Spec L → Spec 𝓞_L`, then transport along `𝒢.gen`) |
| `RegularAtOrigin` | for `B : AbVar L`, `IsRegularLocalRing 𝒪_{B,0}` | STANDARD: a smooth variety over a field is regular |
| `DimAtOrigin` | for `B : AbVar L` with `B.dim = g`, `ringKrullDim 𝒪_{B,0} = g` | STANDARD: dimension theory of varieties at closed points |
| `DimBaseChange` | `(A.baseChange L).dim = A.dim` | STANDARD: dimension is invariant under field extension |

All four are true (§4). They are statements over Mathlib's genuine objects (`AbVar` is the project's
shared abelian-variety structure over Mathlib schemes; `IsRegularLocalRing`, `ringKrullDim`,
`topologicalKrullDim` are Mathlib's). None mentions `ω_𝒢`, `⋀^g`, `secIndex`, or the conclusion.

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
   definition `GroupModel.omega = ⋂_s omegaAt s` needs, proved from Mathlib's scheme API: affine
   charts, noetherianity of `Γ(U)`, stalks on affine opens as localizations, germ-injectivity on the
   integral scheme `Spec 𝓞_L`, and a residue lemma. It uses only that `𝒢 → Spec 𝓞_L` is locally of
   finite type and `e` is a section; smoothness is not used here.
3. *The tangent space glue* (§6): `κ(ξ)` is a fraction field of `𝓞_L` (through `structMap`), so
   `rank_L (L ⊗_{𝓞_L} 𝔪_ξ/𝔪_ξ²) = finrank_{κ(ξ)} (𝔪_ξ/𝔪_ξ²)` (`rank_tensor_cotangent`); with Mathlib's
   `IsRegularLocalRing.iff_finrank_cotangentSpace` this equals `ringKrullDim 𝒪_{𝒢,ξ}` for a regular
   local ring.
4. *Corollary* (§7, `hodgeLattice_lattice_of_regular`): `ω_𝒢` and `⋀^g ω_𝒢` are finitely generated
   and `L · ⋀^g ω_𝒢 = hodgeSpace g` (the base change of the lattice is the Hodge line). Projectivity
   of the rank-one module `⋀^g ω_𝒢` is then the STANDARD fact "finitely generated torsion-free over
   a Dedekind domain is projective", not formalized (Mathlib v4.35 has no lemma in this form;
   searched `Projective` with `Dedekind`/`torsion`: nothing).

**Verdict.** The algebraic half of AN3 is reduced to standard facts about varieties over a field and
one stalk identification. Scheme-theoretic facts Mathlib v4.35 lacks (§5): the dimension theory of
varieties (dimension at closed points, invariance under field extension), "smooth ⇒ regular", and
stalks of a fibre product along a localization of the base.

## 1. Chain of reductions (all arrows proved in Lean)

```
OriginStalkIso ∧ RegularAtOrigin  ──regularOrigin_of──▶  RegularOrigin  (IsRegularLocalRing 𝒪_{𝒢,ξ})
OriginStalkIso ∧ DimAtOrigin ∧ DimBaseChange ──dimOrigin_of──▶ DimOrigin (ringKrullDim 𝒪_{𝒢,ξ} = dim A)
RegularOrigin ∧ DimOrigin ──tangentDim_of_regular──▶ TangentDim (finrank_{κ(ξ)} 𝔪_ξ/𝔪_ξ² = dim A)
TangentDim ──cotangentRank_of_tangentDim──▶ CotangentRank (rank_L (L ⊗ 𝔪_ξ/𝔪_ξ²) = dim A)
omegaLocal : OmegaLocal (theorem) ──omegaFG_of_omegaLocal, omegaSpans_of_omegaLocal──▶ OmegaFG ∧ OmegaSpans
OmegaFG ∧ CotangentRank ∧ OmegaSpans ──hodgeLatticeTheorem_of──▶ HodgeLatticeTheorem
```

Named intermediate theorems: `hodgeLatticeTheorem_of_local` (from `OmegaLocal`, `CotangentRank`),
`hodgeLatticeTheorem_of_cotangentRank` (from `CotangentRank` alone),
`hodgeLatticeTheorem_of_regular` (from `RegularOrigin`, `DimOrigin`),
`hodgeLatticeTheorem_of_abVar` (from the four Props of §0).

## 2. What compiles (VERIFIED)

`lake env lean scratch/hodge-lattice/HodgeLattice.lean`: 0 errors; 9 warnings (deprecation of
`TensorProduct.induction_on`, style linters). `#print axioms` at the end of the file, each
`[propext, Classical.choice, Quot.sound]`: `hodgeLattice_of_lattice`, `hodgeLatticeTheorem_of`,
`hodgeLatticeTheorem_of_local`, `omegaLocal`, `hodgeLatticeTheorem_of_cotangentRank`,
`hodgeLatticeTheorem_of_regular`, `hodgeLattice_lattice_of_regular`,
`hodgeLatticeTheorem_of_abVar`. The file needs `lake build ZInQKernel.HDecomp.Faltings.Models`
first (1m51 on this host). The identity `𝒢.detLattice g = detLat 𝒢.omega g` is `rfl`
(`detLattice_eq`), so the generic algebra applies to the definitions of Models.lean verbatim.

## 3. The proofs in outline

### 3.1 Algebra (§1)

Let `V = K ⊗ M`, `b` a `K`-basis of `V` of the form `1 ⊗ w_j` with `w_j ∈ ω` (it exists since `ω`
spans and `rank V = g`). Then:
- (`exists_clear`) every `v ∈ M` has `D • v = Σ a_j w_j` in `M` for some `0 ≠ D ∈ 𝓞_K`: write
  `1 ⊗ v` in the basis, clear denominators, and use that `M → K ⊗ M` is a localization map
  (`isLocalizedModule_iff_isBaseChange` with `TensorProduct.isBaseChange`), so an element killed
  in `K ⊗ M` is killed by a nonzero scalar;
- (`tmul_ιMulti_mem_span`) `(∏ D_i) • ιMulti v = ιMulti(ψ ∘ a) = det(a) • ιMulti w` where
  `ψ : 𝓞_K^g → M` sends `e_j ↦ w_j`; the second equality is `alt_eq_smulRight` (an alternating map on
  `R^g` with values in any module is `det · F(e)`, from `Basis.ext_alternating`). Hence every
  `1 ⊗ ιMulti v` lies in `K · s₀`, `s₀ = 1 ⊗ ιMulti w`, and `K · s₀ = K ⊗ ⋀^g M`;
- `s₀ ≠ 0`: the `𝓞_K`-alternating map `v ↦ det_b(1 ⊗ v)` induces
  `Ψ : K ⊗ ⋀^g M → K` (`exteriorPower.alternatingMapLinearEquiv`, `LinearMap.liftBaseChange`)
  with `Ψ s₀ = det_b b = 1`;
- finite index: `detLat ω g` lies in the image of `⋀^g ω` (finitely generated, Mathlib's
  `exteriorPower.instFinite`), hence in `𝓞_K · t₀` with `s₀ = d • t₀`, and
  `[𝓞_K t₀ : 𝓞_K s₀] = |N(d)|` (`secIndex_smul` of HodgeData.lean).

### 3.2 `ω_𝒢` is a lattice (§3-§5)

`OmegaLocal`: near every `s ∈ Spec 𝓞_L` there are `a ∉ s` and a finitely generated `N ⊆ ω_{A_L}`
spanning over `L` with `N ≤ omegaAt s'` and `omegaAt s' ⊆ N_{s'}` for all `s' ∈ D(a)`. Proof
(`omegaLocal`): take an affine open `U ∋ e(s)` (`isBasis_affineOpens`) and `D(a) ⊆ e⁻¹U`;
`Γ(U)` is noetherian (`LocallyOfFiniteType.isLocallyNoetherian`, `component_noetherian`), so
`I = ker(e^* : Γ(U) → Γ(e⁻¹U))` has finitely many generators `i_k`; put `N = 𝓞_L-span{d i_k}`.
- `N ≤ omegaAt s'`: the germ of `i_k` at `e(s')` lies in the kernel of the stalk map
  (`dCls_mem_omegaAt`).
- `omegaAt s' ⊆ N_{s'}`: a germ `f` in the kernel at `e(s')` is `b/u` with `b, u ∈ Γ(U)`
  (`IsAffineOpen.isLocalization_stalk`); then `e^* b` has zero germ at `s'`, so `e^* b = 0`
  (`germ_injective_of_isIntegral`), so `b ∈ I = Σ Γ(U) i_k`; the coefficients become
  `𝓞_L`-fractions with denominators outside `s'` by the **residue lemma** (`residue`): every germ at
  `e(s')`, specialized to `ξ`, is `≡ c/t mod 𝔪_ξ` with `t ∉ s'` (the stalk of `Spec 𝓞_L` at `s'` is a
  localization, and `e ≫ π = 𝟙` with `Scheme.Hom.stalkSpecializes_stalkMap`).
- `N` spans: the previous item at the generic point, where `omegaAt = ⊤` (`omegaAt_genericPt` of
  Models.lean).

Local-to-global (`fg_iInf_of_local`, `exists_smul_mem_iInf_of_local`): finitely many `D(a)` cover
`Spec 𝓞_L` (`Ideal.span_eq_top_iff_finite`), and `x ∈ N₀_m` for all maximal `m` implies `x ∈ N₀`.

### 3.3 Tangent space (§6)

`isUnit_structMap`: `c ≠ 0 ⇒ structMap c` is a unit of `𝒪_{𝒢,ξ}` (its image in the function field
of `Spec 𝓞_L` is nonzero; stalk maps are local). With the residue lemma at the generic point this
makes `κ(ξ)` a fraction field of `𝓞_L`. Then `L ≃ₐ[𝓞_L] κ(ξ)` (`IsLocalization.algEquiv`),
`𝔪_ξ/𝔪_ξ²` becomes an `L`-module, `isLocalizedModule_id` gives `IsBaseChange L id`, and
`rank_eq_of_equiv_equiv` compares ranks over `L` and `κ(ξ)`.

## 4. The four remaining statements: truth and references

All four are true for the definitions as they stand (STANDARD; locators UNVERIFIED):
- `OriginStalkIso`. `Spec L → Spec 𝓞_L` is the localization at `𝓞_L ∖ 0`; for any scheme `X` over
  `𝓞_L` and a point `x'` of `X_L` over `x ∈ X`, `𝒪_{X,x} → 𝒪_{X_L,x'}` is an isomorphism (affine
  locally `(B ⊗ L)_{Q'} = B_Q` since `Q ∩ 𝓞_L = 0`; EGA I 3.6 / Stacks "base change by a
  localization", UNVERIFIED). The identity `ξ` of the generic fibre is the image of the point of
  `Spec L` under the unit section, and `𝒢.gen` is a group isomorphism (`gen_hom`), so it sends `ξ`
  to `originPt (A.baseChange L)`.
- `RegularAtOrigin`. `B` is smooth over the field `L`; local rings of smooth `L`-schemes are regular
  (EGA IV 17.5.1 / Stacks tag 00TT region, UNVERIFIED).
- `DimAtOrigin`. `B` is an irreducible (geometrically integral) variety of dimension `g`; the local
  ring at any closed point of an irreducible variety has dimension `g` (Hartshorne I.1.8A and
  II Ex. 3.20, UNVERIFIED). `originPt B` is closed (it is `L`-rational).
- `DimBaseChange`. For a scheme of finite type over a field, `dim X_L = dim X` (EGA IV 4.1.4 /
  Stacks "dimension of fibres under field extension", UNVERIFIED).

Note the project's `AbVar.dim` is `topologicalKrullDim A.X.left : WithBot ℕ∞`, and `A.dim = g` in
`HodgeLatticeTheorem` is the coercion of `g : ℕ`; the Props use the same convention.

## 5. What Mathlib v4.35 lacks (precisely)

Searched in `.lake/packages/mathlib` (VERIFIED by grep; absence claims are about these searches):
1. **Dimension theory of varieties.** No lemma computing `ringKrullDim` of a local ring of a finitely
   generated algebra over a field at a maximal ideal, or `topologicalKrullDim` of a scheme of finite
   type over a field. Present: `MvPolynomial.ringKrullDim_of_isNoetherianRing` (dimension of
   polynomial rings), Noether normalization (`exists_finite_inj_algHom_of_fg`), Krull's height
   theorem; absent: `ringKrullDim` invariance under integral extensions (going up/down to
   dimension), "height of every maximal ideal of an affine domain = dim". Blocks `DimAtOrigin`.
2. **Dimension under field extension.** No lemma relating `topologicalKrullDim` of `X ×_K L` and of
   `X`. Blocks `DimBaseChange`.
3. **Smooth ⇒ regular.** `IsRegularLocalRing` exists (`RingTheory/RegularLocalRing/Defs.lean`, with
   `iff_finrank_cotangentSpace`, and `RegularLocalRing/Polynomial.lean` for localizations of
   polynomial rings), but no file under `RingTheory/Smooth` mentions `IsRegularLocalRing` or
   `ringKrullDim`. Blocks `RegularAtOrigin`. (A route: étale-locally `B` is `𝔸^g_L`, plus "étale
   preserves regularity and dimension"; both missing.)
4. **Stalks of base change along a localization.** No lemma identifying stalks of `X ×_S Spec 𝒪_{S,η}`
   (or `X ×_{Spec R} Spec R_f`-type pullbacks beyond open immersions) with stalks of `X`. Blocks
   `OriginStalkIso`; it is the one item that needs no new theory, only work with
   `pullbackSpecIso` and localizations (SPECULATIVE size: a few hundred lines).

Present and used: `IsAffineOpen.isLocalization_stalk`, `germ_injective_of_isIntegral`,
`Scheme.Hom.germ_stalkMap_apply`, `Scheme.Hom.stalkSpecializes_stalkMap_apply`,
`LocallyOfFiniteType.isLocallyNoetherian`, `IsLocallyNoetherian.component_noetherian`,
`isBasis_affineOpens`, `basicOpen_eq_of_affine`, `Ideal.Cotangent.smul_eq_zero_of_mem`,
`IsRegularLocalRing.iff_finrank_cotangentSpace`, `exteriorPower.ιMulti_span`,
`exteriorPower.alternatingMapLinearEquiv`, `exteriorPower.instFinite`, `Basis.ext_alternating`,
`isLocalizedModule_iff_isBaseChange`, `isLocalizedModule_id`, `rank_eq_of_equiv_equiv`.

## 6. Integration notes

- The file imports only `ZInQKernel.HDecomp.Faltings.Models`; as a build module it would go next to
  it (e.g. `ZInQKernel/HDecomp/Faltings/HodgeLatticeProof.lean`). It does not touch the upstream
  contract (`HodgeLatticeTheorem` is HDecomp glue, not one of the five registered hypotheses).
- In h-decomposition.md, `HodgeLatticeTheorem` can be replaced by the four Props of §0. They are
  textbook facts rather than refereed literature theorems; three are about varieties over a field
  and can be crowdsourced independently of the model theory, and `OriginStalkIso` is glue.
- `HodgeLatticeTheorem` only makes R19-R21 non-vacuous together with AN3's analytic Props
  (`AnalyticUniformizationExists`, `AnalyticUniformizationUnique`), which this task did not touch.

## 7. Unchecked items

- All literature/textbook locators in §4 are from memory (UNVERIFIED).
- Projectivity and invertibility of `⋀^g ω_𝒢` (the "projective of rank one" phrasing of the task)
  are STANDARD consequences of §7's corollary, not proved in Lean; `HodgeLatticeTheorem` as stated
  does not ask for them.
- No independent (model) review of the new Props was run.
