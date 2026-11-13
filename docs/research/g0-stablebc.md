# g0-stablebc: the glue piece `StableHeightBaseChange`

Task g0-stablebc, 2026-11-13. Lean: `scratch/g0-stablebc/StableBC.lean`, assembled from
`Defs.part` (lines 16667-18351 of `scratch/g0-split/Split.lean`, copied verbatim) and
`Main.part` (new). Log: `scratch/g0-stablebc/log.md`. `TestComp.lean` is the small test file in
which the category-theory part was developed.

## 1. Result

**`StableHeightBaseChange` (missing piece 6 of g0-split) is proved from one smaller glue
statement, `HodgeLineBaseChange`.** That statement concerns the group models alone: no Hodge data,
no metrized models, no heights. It is the geometric content of h5-neron's glue H4a. For a base
change `𝒢'/𝓞_{L'}` of a group model `𝒢/𝓞_L`, the natural map
`ψ : ⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` has five properties:
- it is semilinear;
- it is injective;
- it preserves "being a line";
- it carries the lattice: `⋀^g ω_{𝒢'} = 𝓞_{L'}·ψ(⋀^g ω_𝒢)`;
- it is compatible with analytic uniformizations and the coefficients they compute.

Everything else is proved in Lean:
- `BaseChangeCompIso`: `(A_L)_M ≅ A_M` as group schemes.
- h5-neron's `GroupModelBaseChangeExists` (glue H4b). This is the statement on which h5-neron hit
  a kernel deterministic timeout.
- The construction of the Hodge data of `𝒢'` from those of `𝒢`
  (`metrizationBaseChange_of_hodgeLine`).
- The Arakelov half of H4a: base change of Hodge data preserves the model height
  (`modelHeight_eq_of_isHodgeBaseChange`). Its finite part is `secIndex_baseChange`:
  `#(Λ'/𝓞_{L'}ιη) = #(Λ/𝓞_Lη)^{[L':L]}` for every rank-one lattice.
- Transport of group models along `(A_L)_M ≅ A_M`, and the two infimum arguments.

VERIFIED (each by `lake env lean`; `#print axioms` gives `[propext, Classical.choice, Quot.sound]`
for every theorem below):
- `scratch/g0-stablebc/StableBC.lean`: 0 errors, no `sorry` (run10).
- `scratch/g0-stablebc/SplitPlus.lean`, which is g0-split's `Split.lean` with this file's new part
  appended over Split's own objects: 0 errors, no `sorry` (run11). It proves
  `G0StableBC.glueOutputs_of_leaves_hodgeLine`, g0-split's main theorem
  `HSyn.glueOutputs_of_leaves` with the hypothesis `hBC : StableHeightBaseChange` replaced by
  `HodgeLineBaseChange`, and `G0StableBC.split_piece_iff :
  HSyn.G0Split.StableHeightBaseChange ↔ G0StableBC.StableHeightBaseChange := Iff.rfl`.

| Lean name | statement | status |
|---|---|---|
| `StableHeightBaseChange` | the piece, copied verbatim from `Split.lean` (docstring and body) | proved from `HodgeLineBaseChange` |
| `stableHeightBaseChange_of_hodgeLine` | `HodgeLineBaseChange → StableHeightBaseChange` | **proved** |
| `metrizationBaseChange_of_hodgeLine` | `HodgeLineBaseChange → MetrizationBaseChange` | **proved** |
| `stableHeightBaseChange_of_metrization` | `MetrizationBaseChange → StableHeightBaseChange` | **proved** |
| `modelHeightBaseChangeLE_of_metrization` | `MetrizationBaseChange → ModelHeightBaseChangeLE` | **proved** |
| `stableHeightBaseChange_of_modelHeightBaseChangeLE` | `ModelHeightBaseChangeLE → StableHeightBaseChange` | **proved** |
| `stableHeightBaseChange_of_modelHeightBaseChange` | the same from h5-neron's H4a (`=`) | **proved** |
| `stableHeightBaseChange_of_glue` | the piece from `BaseChangeCompIso`, H4b and H4a `≤` | **proved** |
| `baseChangeCompIso : BaseChangeCompIso` | `∃ e : ((A.baseChange L).baseChange M).X ≅ (A.baseChange M).X, IsMonHom e.hom` for a scalar tower `K → L → M` | **proved** (new glue) |
| `groupModelBaseChangeExists : GroupModelBaseChangeExists` | h5-neron's H4b, verbatim: a group model `𝒢/𝓞_L` has a base change `𝒢'/𝓞_{L'}` that is again a `GroupModel` of `A` | **proved** |
| `transportModel`, `transportMetrized`, `transportModel_height_le` | a (metrized) group model of `A_L` is one of `B_L` along a group-scheme iso `A_L ≅ B_L`, with no larger height | **proved** |
| `modelHeight_eq_of_isHodgeBaseChange` | `IsHodgeBaseChange D D' ι → D'.modelHeight = D.modelHeight` | **proved** |
| `secIndex_baseChange`, `secIndex_map`, `secIndex_nsmul_mem` | the index computations behind the previous row | **proved** |
| `compositum` | copied from h5-neron (proved there) | proved |
| `ModelHeightBaseChangeLE` | `IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height ≤ 𝒢.height` (the `≤` half of H4a) | glue, follows from the rows below |
| `MetrizationBaseChange` | for `IsBaseChangeOf 𝒢' 𝒢` and a metrization `Mm` of `𝒢` (dimension `g`), there are a metrization `Mm'` of `𝒢'` and `ι` with `IsHodgeBaseChange Mm.hodge Mm'.hodge ι` | glue, follows from the next row |
| `HodgeLineBaseChange` | for `IsBaseChangeOf 𝒢' 𝒢` and `g`: there is `ψ : 𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g`, semilinear, injective on nonzero vectors, preserving finrank 1, with `𝒢'.detLattice g = span_{𝓞_{L'}} ψ(𝒢.detLattice g)`, and for every analytic uniformization `Φ` of `𝒢(ℂ)_{τ'|_L}` there is one `Φ'` of `𝒢'(ℂ)_{τ'}` with the same kernel such that every coefficient map computed by `Φ` on wedges has its extension along `ψ` computed by `Φ'` on wedges | **glue, open** |

`IsHodgeBaseChange D D' ι` has five fields:
- `ι` is `L`-semilinear over `L → L'`;
- `ι` is injective on nonzero vectors;
- `D'.lattice = 𝓞_{L'}·ι(D.lattice)`;
- `D'.periods τ' = D.periods (τ'|_L)`;
- `D'.coeff τ' (ι v) = D.coeff (τ'|_L) v`.

**The remaining input is glue, not a leaf, and no leaf is used.** `HodgeLineBaseChange` is a
property of def-faltings' definitions, true by the standard argument (h5-neron §2):
- `ι` is the natural map `⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` induced by `𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`;
- `⋀^g ω_{𝒢'} = 𝓞_{L'}·ι(⋀^g ω_𝒢)`, because formation of `e*Ω¹` of a smooth group scheme commutes
  with base change (EGA IV 17.2.3, UNVERIFIED locator);
- at `τ'`, the uniformization of `𝒢(ℂ)_{τ'|_L}` composed with the bijection
  `𝒢(ℂ)_{τ'|_L} ≅ 𝒢'(ℂ)_{τ'}` given by the pullback (STANDARD).

## 2. The proof

`stableFaltingsHeight A = ⨅_{E : FinExt K} ⨅_{𝒢 : GroupModel A E.L} h(𝒢)`
(`stableFaltingsHeight_eq_iInf_height`, def-faltings, proved). Take this form for `A` and for
`A_L`.

- **`h(A) ≤ h(A_L)`.** Let `M ⊇ L` be a number field and `𝒢` a group model of `(A_L)_M`. Give
  `M` the `K`-algebra structure `K → L → M`. `baseChangeCompIso` gives `e : (A_L)_M ≅ A_M`.
  `transportModel e 𝒢` is the same `𝒢` with `gen` composed with `e`, so it is a group model of
  `A_M`. Its metrizations include those of `𝒢`: the Hodge line, the lattice `⋀^g ω`, the complex
  points and the evaluation maps depend only on `𝒢.G` and its group structure, not on `gen`. So
  `h(transportModel e 𝒢) ≤ h(𝒢)`.
- **`h(A_L) ≤ h(A)`.** Let `E ⊇ K` and `𝒢` a group model of `A_E`. Let `M` be a compositum of
  `E` and `L` over `K` (`compositum`). H4b, now proved, gives the base change `𝒢'/𝓞_M`, a group
  model of `A_M`, and `ModelHeightBaseChangeLE` gives `h(𝒢') ≤ h(𝒢)`. Transport along `e⁻¹`
  (`IsMonHom e.inv` is a Mathlib instance) makes `𝒢'` a group model of `(A_L)_M` with no larger
  height.

**The workaround for h5-neron's kernel timeout (VERIFIED: it compiles).** h5-neron built the
generic-fibre isomorphism of `𝒢 ×_{𝓞_L} 𝓞_{L'}` as one chain of six isomorphisms over the concrete
schemes `Spec 𝓞_L`, `Spec L`, …, with `eqToIso` along the commuting squares. Checking its
`IsMonHom` timed out in the kernel. Here the proof has three steps:
1. `exists_pbPaste f g h (sq : f ≫ g = h) G` is proved for arbitrary schemes. `subst sq` removes
   the equation, and then the components of `Over.pullbackComp` are monoid maps (h5-neron's
   `isMonHom_pbCompInv`). This removes `eqToIso` completely.
2. `exists_pbSquare` pastes two such squares and one group-scheme isomorphism on a leg. It is
   also proved for arbitrary schemes, so no concrete instance term appears in its proof.
3. Only then are the lemmas instantiated: at `Spec L' → Spec 𝓞_{L'} → Spec 𝓞_L` and
   `Spec L' → Spec L → Spec 𝓞_L` (h5-neron's `square1`), and at `K → L → M`. The last composition,
   `IsMonHom (e.hom ≫ c.hom)`, is given as an explicit term
   `@CategoryTheory.instIsMonHomComp … e.hom c.hom he hc`. Instance search cannot see through
   `AbVar.baseChange` to match the middle `MonObj` instance. Unification at default transparency
   can, and the kernel accepts the result quickly: the whole file checks in 17 s (run2) to 1m43
   (run3, under load).

**The Arakelov half (proved).** Pick `0 ≠ η ∈ Λ = ⋀^g ω_𝒢`. The coordinates `c ↦ c·η` and
`c ↦ c·ιη` turn `Λ` into an `𝓞_L`-submodule `I ∋ 1` of `L`, and `Λ'` into `𝓞_{L'}·I`.
`I` is a fractional ideal: its index `N = #(Λ/𝓞η)` kills `Λ/𝓞η` (`secIndex_nsmul_mem`).
def-faltings' index formula `#(I/𝓞x)·N(I) = |N(x)|` at `x = 1` and its
`N(I𝓞_{L'}) = N(I)^{[L':L]}` give `#(Λ'/𝓞ιη) = #(Λ/𝓞η)^{[L':L]}`. For the archimedean sum,
`∑_{τ'} f(τ'|_L) = [L':L]·∑_σ f(σ)` (`sum_embeddings_comp`). With
`[L':ℚ] = [L':L][L:ℚ]`, the two model heights in Faltings' formula `modelHeight_eq` agree.

h5-neron's finding stands: the Néron model does not commute with base change, only its identity
component does. It does not affect this piece. The argument above never uses Néron models. It uses
base change of an arbitrary smooth group model (H4b), which always holds, and the height
inequality H4a `≤` for that base change.

## 3. Checks

- **The statement is unchanged.** `StableHeightBaseChange` in `Main.part` is a verbatim copy of
  `Split.lean` line 19491, over the verbatim copy of def-faltings' objects (`Defs.part`). The
  copies of h5-neron's `IsBaseChangeOf`, `ModelHeightBaseChange` and `GroupModelBaseChangeExists`
  are verbatim too. They are elaborated over this file's `ZInQ.DefFaltings.AbVar`, the same
  structure as the kernel's `PkgI3.AbVar` (`LeafAdopt.abVarEquiv`).
- **The piece is not vacuous.** Its proof uses only the infimum description of the height, so it
  holds whatever the value is, including `⊤`. That is the right behaviour for a property of the
  definition. Its truth for the published height is g0-split §3's point (H5).
- **`HodgeLineBaseChange`, hence `MetrizationBaseChange`, is true** (STANDARD argument, no Lean
  proof). Take the honest base
  change, with `Φ' = β ∘ Φ`, where `β : 𝒢(ℂ)_{τ'|_L} ≅ 𝒢'(ℂ)_{τ'}` is the pullback bijection.
  Then `ker Φ' = ker Φ`, which gives `periods`. For a germ `f` of `𝒢` with pullback `f'`:
  `evalAt' (β p) f' = evalAt p f`, hence `jacDet' Φ' f' = jacDet Φ f` and
  `wedge' f' = ι (wedge f)`. So the coefficient map with `coeff' τ' (ι v) = coeff (τ'|_L) v`,
  extended `τ'`-semilinearly, satisfies `arch`. `𝒢'` is an arbitrary group model with
  `IsBaseChangeOf 𝒢' 𝒢`; the iso `𝒢'.G ≅ 𝒢.G ×_{𝓞_L} 𝓞_{L'}` transports all of this, and the
  `gen` of `𝒢'` plays no role.
- `open scoped Obj` is used only inside `section PbPaste`, after the Props are stated. So the
  statements' instances are the `AbVar.grp` / `GroupModel.grp` fields. The proofs check against
  the Props as stated without the scoped instances.
- An independent read-only model review checked `BaseChangeCompIso`, `ModelHeightBaseChangeLE`,
  `IsHodgeBaseChange` and `MetrizationBaseChange`, and the verbatim copies. It found all four
  statements true and none vacuous. The quantifier order and the direction of `τ'|_L` are right.
  It flagged two docstring inaccuracies, both fixed: "strictly weaker" became "implied by", and
  the verbatim docstring of the piece was restored. A second review covers
  `HodgeLineBaseChange` (§5). No human review.

## 4. What remains

- `HodgeLineBaseChange` (glue, size L, SPECULATIVE). It needs:
  - the stalk map `𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}` along `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'} → 𝒢`, with
    `cotangent' = cotangent ⊗_L L'`, defining `ψ` and giving finrank and injectivity;
  - `omegaAt` at every point of `Spec 𝓞_{L'}` and `⋀^g` under base change, for the lattice clause;
  - the pullback bijection `𝒢'(ℂ)_{τ'} ≅ 𝒢(ℂ)_{τ'|_L}`, compatible with `evalAt`, `germAlong` and
    `jacDet`, for the uniformization clause.

  No Arakelov or Hodge-data work is left.
- Integration:
  - `baseChangeCompIso`, `exists_pbPaste`, `exists_pbSquare` and `groupModelBaseChangeExists`
    can replace the commented-out attempt in `scratch/h5-neron/BaseChange.lean`. They need
    `open scoped Obj` and `isMonHom_pbCompInv`.
  - H5 (`stableFaltingsHeight_eq_neron`) then loses the hypothesis `hbcE`.
  - In `Split.lean`, `hBC : StableHeightBaseChange` can be replaced by
    `hHL : HodgeLineBaseChange` through `stableHeightBaseChange_of_hodgeLine`. This is checked in
    `SplitPlus.lean`, theorem `glueOutputs_of_leaves_hodgeLine`. The same
    statement also gives the `≤` half of h5-neron's H4a
    (`modelHeightBaseChangeLE_of_metrization`). H4a `=` needs, in addition, that every
    metrization of `𝒢'` has height at least that of `𝒢` (the converse direction), which is not
    needed here.
