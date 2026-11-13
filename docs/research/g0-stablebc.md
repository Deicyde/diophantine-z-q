# g0-stablebc: the glue piece `StableHeightBaseChange`

Task g0-stablebc, 2026-11-13. Lean: `scratch/g0-stablebc/StableBC.lean`, assembled from
`Defs.part` (lines 16667-18351 of `scratch/g0-split/Split.lean`, copied verbatim) and
`Main.part` (new). Log: `scratch/g0-stablebc/log.md`. `TestComp.lean` is the small test file in
which the category-theory part was developed.

## 1. Result

**`StableHeightBaseChange` (missing piece 6 of g0-split) is proved from one smaller glue
statement, `ModelHeightBaseChangeLE`.** That statement is the `≤` half of h5-neron's glue H4a:
base change of a group model does not raise its height. The other two inputs are now proved:

- `BaseChangeCompIso`: `(A_L)_M ≅ A_M` as group schemes;
- h5-neron's `GroupModelBaseChangeExists` (glue H4b). This is the statement on which h5-neron hit
  a kernel deterministic timeout.

VERIFIED: `lake env lean scratch/g0-stablebc/StableBC.lean` gives 0 errors and no `sorry`
(run3). `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for each of the following:

| Lean name | statement | status |
|---|---|---|
| `StableHeightBaseChange` | the piece, copied verbatim from `Split.lean` | proved from `ModelHeightBaseChangeLE` |
| `stableHeightBaseChange_of_modelHeightBaseChangeLE` | `ModelHeightBaseChangeLE → StableHeightBaseChange` | **proved** |
| `stableHeightBaseChange_of_modelHeightBaseChange` | the same from h5-neron's H4a (`=`) | **proved** |
| `stableHeightBaseChange_of_glue` | the piece from `BaseChangeCompIso`, H4b, H4a `≤` | **proved** |
| `baseChangeCompIso : BaseChangeCompIso` | `∃ e : ((A.baseChange L).baseChange M).X ≅ (A.baseChange M).X, IsMonHom e.hom` for a scalar tower `K → L → M` | **proved** (new glue) |
| `groupModelBaseChangeExists : GroupModelBaseChangeExists` | h5-neron's H4b, verbatim: a group model `𝒢/𝓞_L` has a base change `𝒢'/𝓞_{L'}` that is again a `GroupModel` of `A` | **proved** |
| `transportModel`, `transportMetrized`, `transportModel_height_le` | a (metrized) group model of `A_L` is one of `B_L` along a group-scheme iso `A_L ≅ B_L`, with no larger height | **proved** |
| `compositum` | copied from h5-neron (proved there) | proved |
| `ModelHeightBaseChangeLE` | `IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height ≤ 𝒢.height` | **glue, open** |
| `modelHeightBaseChangeLE` | `ModelHeightBaseChange → ModelHeightBaseChangeLE` | proved (trivial) |

The single remaining input is glue, not a leaf. It is a property of def-faltings' definition of
the model height, and it is true by the standard argument (h5-neron §2): `𝒢` is smooth, so
`e*Ω¹` commutes with base change, and `⋀^g ω_{𝒢'} = ⋀^g ω_𝒢 ⊗ 𝓞_{L'}`. The Arakelov degree is
multiplied by `[L':L]`. Each `τ' : L' → ℂ` restricts to `τ = τ'|_L`, and `𝒢'(ℂ)_{τ'} = 𝒢(ℂ)_τ`
with the same uniformization (STANDARD). Its Arakelov half for rank-one ideal data is already in
the file, as def-faltings' `HodgeData.modelHeight_ofIdeal_baseChange`. No leaf is used.

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
- **`ModelHeightBaseChangeLE` is true** (SPECULATIVE in the sense of no Lean proof; the argument
  is STANDARD). For any metrization `Mm` of `𝒢` of dimension `g`, the base-changed data give a
  metrization of `𝒢'` of dimension `g` with the same model height. Equality holds, h5-neron §7.
  The `gen` of `𝒢'` is irrelevant, as in `IsBaseChangeOf`.
- `open scoped Obj` is used only inside `section PbPaste`, after the Props are stated. So the
  statements' instances are the `AbVar.grp` / `GroupModel.grp` fields. The proofs check against
  the Props as stated without the scoped instances.

## 4. What remains

- `ModelHeightBaseChangeLE` (glue, size L, SPECULATIVE): flat base change of `ω` for the local
  ring of `𝒢'` at its generic unit (`𝒪_{𝒢',ξ'}` versus `𝒪_{𝒢,ξ} ⊗ L'`), of `omegaAt` at every point
  of `Spec 𝓞_{L'}`, and of `⋀^g`; the bijection `𝒢'(ℂ)_{τ'} ≅ 𝒢(ℂ)_{τ'|L}` (pullback universal
  property), compatible with `evalAt` and `jacDet`; and the Arakelov count (sums over embeddings
  `sum_embeddings_comp` and norms of extended ideals `absNorm_extendedHom`, both proved in the
  file).
- Integration: `baseChangeCompIso`, `exists_pbPaste`, `exists_pbSquare` and
  `groupModelBaseChangeExists` can replace the commented-out attempt in
  `scratch/h5-neron/BaseChange.lean`. They need `open scoped Obj` and
  `isMonHom_pbCompInv`. H5 (`stableFaltingsHeight_eq_neron`) then loses the hypothesis `hbcE`.
  In `Split.lean`, the hypothesis `hBC : StableHeightBaseChange` can be replaced by
  `hBC' : ModelHeightBaseChangeLE` through `stableHeightBaseChange_of_modelHeightBaseChangeLE`.
