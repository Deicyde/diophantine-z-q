# fold notes: h5-neron

Source: `scratch/h5-neron/H5Neron.lean` (881 lines, self-contained, imports
`ZInQKernel.HDecomp.Faltings.Leaves`), report `docs/research/h5-neron.md`.
Fragment: `scratch/leaf-adopt3/fold/h5-neron.lean` (930 lines, `section H5NeronSec ... end H5NeronSec`).
New declarations are in `ZInQ.H5Neron`. Insert after hodge-lattice; there is no dependency either way.

## The one `sorry` occurrence
It is in the module docstring ("no `sorry`, no `axiom`"), not in code. It is reworded in the fragment.
Code-free: the other part files (`Neron.lean`, `ZeroAV.lean`, `Reduction.lean`, `ProductModel.lean`)
are subsumed by H5Neron.lean. `BaseChange.lean` (partial H4b) is **not** folded: its main theorems
`bcGen_isMonHom` / `groupModelBaseChangeExists` exist only inside a comment (kernel deterministic
timeout). Only helper lemmas compile there (`isMonHom_pbCompHom`, `isMonHom_pbCompInv`,
`isMonHom_pbEq`, `square1`, `square2`, `bcGen`), and nothing in H5Neron.lean uses them.

## Changes from the source
- Dropped the `import` line and the 27 `#print axioms` lines (all `[propext, Classical.choice, Quot.sound]`
  per the report): `NeronProp.lift/uniqueIso/tensor/of_iso`, `GroupModel.IsNeronModel.lift/uniqueIso`,
  `isNeronModel_of_isProductModel`, `stableFaltingsHeight_add_le`, `modelHeight_dim_zero`,
  `pts_subsingleton`, `no_metrized_succ`, `trivModel_isNeronModel`, `stableFaltingsHeight_zero`,
  `groupModel_height_zero`, `neronModelMinimal_zero`, `stableHeightFinite_zero`, `R19_zero`, `R20_zero`,
  `R21_zero`, `compositum`, `stableFaltingsHeight_eq_neron`, `neronModelExists_zero`,
  `semistableNeronIdentityComponent_zero`, `glue_zero`, `stableFaltingsHeight_eq_neron_all`,
  `productGroupModelExists`, `stableFaltingsHeight_add_le'`.
- **Deleted the 4 lines `open PkgI3 (AbVar)`.** The kernel's `ZInQ.DefFaltings` works over `PkgI3.AbVar`.
  Leaves.lean's `DefFaltingsSec` has the copy `ZInQ.DefFaltings.AbVar`, and `GroupModel`,
  `NeronModelMinimal`, `stableFaltingsHeight`, `LeafAdopt.H5` are over the copy. In
  `namespace ZInQ.H5Neron` (not a sub-namespace of `DefFaltings`), `open DefFaltings` already brings
  `ZInQ.DefFaltings.AbVar`. Keeping `open PkgI3 (AbVar)` would make the bare `AbVar` ambiguous (two
  open declarations, both elaborate), so the lines must go. Everything is now over
  `ZInQ.DefFaltings.AbVar`.
- **New kernel-substitute declaration** `ZInQ.H5Neron.AbVar.zero (K) [Field K] : ZInQ.DefFaltings.AbVar K`.
  It is the verbatim body of `PkgI3.AbVar.zero` (Objects.lean ~396; Leaves.lean ~2764), placed just
  before `section ZeroAV`. The source used `PkgI3.AbVar.zero`; inside `ZInQ.H5Neron` the name
  `AbVar.zero` now resolves to the new one, because the namespace match comes first. The body needs the
  global instance `PkgI3.AbVar.geometricallyIntegral_id_spec` (Leaves.lean ~2752, present).
- Statements and proofs otherwise verbatim. New bridges are appended (below).

## Kernel vs Leaves.lean check
I diffed `ZInQKernel/HDecomp/Faltings/{HodgeData,IdealLines,Models,Height,Leaves}.lean` against
Leaves.lean 16714-18616. The only differences are the `AbVar` copy and the
`structMapOn`/`origin` namespaces (`_root_.PkgI3.AbVar.*` vs `ZInQ.DefFaltings.AbVar.*`; not used by
name here). So `NeronModelMinimal`, `StableHeightFinite`, `IsNeronModel`, `stableFaltingsHeight`,
`stableFaltingsHeight_eq_iInf_height`, `le_stableFaltingsHeight`, `stableFaltingsHeight_le`,
`MetrizedModel`, `HodgeData.modelHeight_of_span`, `torusMetricSq`, `isogDeg`, `ptObj`, `IsIsogeny`,
`grKappa`, ... are identical. No ZInQ.H5Neron name exists in Leaves.lean, `parts/` or other fold files.
`LeafAdopt.H5` (Leaves.lean ~18786) is `ZInQ.DefFaltings.StableHeightFinite ∧ ZInQ.DefFaltings.NeronModelMinimal`,
the same Props h5-neron uses.

## What is actually proved (precise)
- **No theorem concludes `LeafAdopt.H5`, nor `StableHeightFinite`, nor `NeronModelMinimal` for general
  `A`.**
  - `NeronModelMinimal` is a **hypothesis** of `stableFaltingsHeight_eq_neron(_all)` and of
    `stableFaltingsHeight_add_le(')`.
  - `StableHeightFinite` appears only as the zero-AV instance `stableHeightFinite_zero`. It needs AN3
    (`AnalyticUniformizationExists`) and `HodgeLatticeTheorem` for the index set to be nonempty, plus a
    lower bound; none of that is in this task.
  - So the bundle field `ResearchLeaves.h5 : LeafAdopt.H5` stays. h5-neron *refines* what H5 is used
    for, but does not replace it in Lean.
- `stableFaltingsHeight_eq_neron_all (hN1 : NeronModelExists) (hN2 : SemistableNeronIdentityComponent) (hmin : NeronModelMinimal) (hbc : ModelHeightBaseChange) (hbcE : GroupModelBaseChangeExists) (hop : OpenSubgroupHeight) (K) [Field K] [NumberField K] (A : AbVar K)`
  gives:
  - `∃ L₀ … (𝒩₀ : GroupModel A L₀), 𝒩₀.IsNeronModel ∧ stableFaltingsHeight A = 𝒩₀.height ∧`
  - `∀ L' ⊇ L₀ (IsScalarTower K L₀ L') (𝒩' : GroupModel A L'), 𝒩'.IsNeronModel → stableFaltingsHeight A = 𝒩'.height`.

  This is the form R19-R21 need. `stableFaltingsHeight_eq_neron` is its first half.
- `stableFaltingsHeight_add_le' (hN1 : NeronModelExists) (hmin : NeronModelMinimal) (hH : ProductModelHeight) (A B C : AbVar K) (hC : IsProductAbVar C A B) : stableFaltingsHeight A + stableFaltingsHeight B ≤ stableFaltingsHeight C`
  (EReal). Glue P1 `productGroupModelExists : ProductGroupModelExists` is proved.
- Zero-AV instances: N1, N2, the glue shapes, `NeronModelMinimal`, `StableHeightFinite`, R19-R21 for
  `AbVar.zero K`, and `stableFaltingsHeight (AbVar.zero K) = 0`. These are non-vacuity checks only.

## Bridges appended (new, in `ZInQ.H5Neron`; take the bundle field `h5` as the source of `NeronModelMinimal`)
- `stableFaltingsHeight_eq_neron_all_of_H5 (h5 : LeafAdopt.H5) (hN1 : NeronModelExists) (hN2 : SemistableNeronIdentityComponent) (hbc : ModelHeightBaseChange) (hbcE : GroupModelBaseChangeExists) (hop : OpenSubgroupHeight) (K) [Field K] [NumberField K] (A : ZInQ.DefFaltings.AbVar K) : <conclusion of _eq_neron_all>`
  (proof: `stableFaltingsHeight_eq_neron_all hN1 hN2 h5.2 hbc hbcE hop K A`).
- `stableFaltingsHeight_add_le_of_H5 (h5 : LeafAdopt.H5) (hN1 : NeronModelExists) (hH : ProductModelHeight) (A B C) (hC : IsProductAbVar C A B) : sFH A + sFH B ≤ sFH C`.
- `heightAdditivity_unfolded (hN1 : NeronModelExists) (hmin : ZInQ.DefFaltings.NeronModelMinimal) (hH : ProductModelHeight)`
  gives g0-split's `HeightAdditivity` with `IsProductOf` unfolded:
  `∀ L [Field L] [NumberField L] (P A Z : ZInQ.DefFaltings.AbVar L) (p₁ : P.X ⟶ A.X) (p₂ : P.X ⟶ Z.X), IsMonHom p₁ → IsMonHom p₂ → IsIso (CartesianMonoidalCategory.lift p₁ p₂) → ∀ a z p : ℝ, sFH A = a → sFH Z = z → sFH P = p → a + z ≤ p`.
  Proof: `IsProductAbVar P A Z` via `asIso (lift p₁ p₂)` (`asIso_hom`, `lift_fst`/`lift_snd`), then
  `stableFaltingsHeight_add_le'`, rewrite, `exact_mod_cast` (EReal coe_add / coe_le_coe). **Not
  compiled.**

## New leaf / glue Props (as in the source, statement-identical)
- **Leaf N1** `ZInQ.H5Neron.NeronModelExists`: every `A_L` (`A : AbVar K`, `L` a number field over `K`)
  has a group model with `IsNeronModel` (BLR 1.2/1, 1.4/3; UNVERIFIED locators).
- **Leaf N2** `ZInQ.H5Neron.SemistableNeronIdentityComponent`: `∃ L₀`, Néron `𝒩₀`; `∀ L' ⊇ L₀`, every
  Néron `𝒩'` has a common open subgroup model `𝒰` with a base change `𝒱` of `𝒩₀` (SGA 7 IX 3.6 + 3.3;
  SGA 3 VI_B 3.10; UNVERIFIED).
- **Glue**:
  - `ModelHeightBaseChange` (H4a);
  - `GroupModelBaseChangeExists` (H4b; partial attempt in BaseChange.lean);
  - `OpenSubgroupHeight` (M6);
  - `ProductModelHeight` (P2);
  - the existing `ZInQ.DefFaltings.NeronModelMinimal`. The report argues it is glue, not a leaf
    (mapping property + `ω_𝒩 ⊆ ω_𝒢` + `modelHeight_le_of_le`).
- Helper defs: `NeronProp`, `IsProductAbVar`, `bcProd`, `IsProductModel`, `IsBaseChangeOf`,
  `IsOpenSubgroupModel`, `jL`.

The report's recommendation is to replace leaf H5 by N1 + N2 as leaves, keep `StableHeightFinite` as
correctness of the definition, and add the four H5 glue statements and P2 as glue targets. That is a
bundle redesign, left to the orchestrator.

## g0-split comparisons
- **`HSyn.G0Split.HeightAdditivity`** (parts/70_g0.lean ~138) is
  `∀ L [Field L] [NumberField L] (P A Z : ZInQ.DefFaltings.AbVar L), IsProductOf P.X A.X Z.X → ∀ a z p : ℝ, sFH A = a → sFH Z = z → sFH P = p → a + z ≤ p`,
  with `IsProductOf P A Z := ∃ p₁ p₂, IsMonHom p₁ ∧ IsMonHom p₂ ∧ IsIso (lift p₁ p₂)`.
  - It **follows** from N1 + `NeronModelMinimal` + `ProductModelHeight`.
  - `IsProductOf` gives `IsProductAbVar` via `asIso (lift p₁ p₂)`, so `stableFaltingsHeight_add_le'`
    applies, and the real numbers come back by `exact_mod_cast`.
  - Bridge, to be placed after g0-split's definitions (inside `namespace HSyn`):
    ```lean
    theorem G0Split.heightAdditivity_of_h5neron (hN1 : ZInQ.H5Neron.NeronModelExists)
        (hmin : ZInQ.DefFaltings.NeronModelMinimal) (hH : ZInQ.H5Neron.ProductModelHeight) :
        G0Split.HeightAdditivity :=
      fun L _ _ P A Z ⟨p₁, p₂, h₁, h₂, h⟩ =>
        ZInQ.H5Neron.heightAdditivity_unfolded hN1 hmin hH L P A Z p₁ p₂ h₁ h₂ h
    ```
    (`hmin` can be `r.h5.2`). This assumes g0's `lift` is `CartesianMonoidalCategory.lift`, which is
    the only `lift` that typechecks there.
  - So the missing piece 5 can be replaced by N1 + P2 (+ H5).
- **`HSyn.G0Split.StableHeightBaseChange`** (`∀ K L number fields, [Algebra K L], A : ZInQ.DefFaltings.AbVar K, sFH (A.baseChange L) = sFH A`)
  does **not** follow from anything proved in h5-neron.
  - Route: apply `stableFaltingsHeight_eq_neron_all` to both `A` (over `K`) and `A_L` (over `L`), then
    take a compositum `L'''` containing `L` and both `L₀`'s (`compositum` handles only two fields over
    one base, so it must be applied twice, with the `IsScalarTower` bookkeeping for `K → L → L'''`).
  - Missing transport glue: Néron models of `A_{L'''}` and of `(A_L)_{L'''}` must have the same height.
    That needs `GroupModel (A.baseChange L) L''' ≃ GroupModel A L'''`, preserving `IsNeronModel` and
    `height`, along the pullback-composition iso `(A_L)_{L'''} ≅ A_{L'''}`. This is the same
    `IsMonHom`-along-`Over.pullbackComp` problem on which BaseChange.lean's H4b attempt timed out in
    the kernel.
  - So StableHeightBaseChange would follow from N1, N2, `NeronModelMinimal`, H4a, H4b, M6 and one more
    transport glue (not stated in Lean by the task). Not attempted here.

## Expected trouble spots
- `AbVar.zero` resolution and its body. If `dsimp; infer_instance` fails for the instances, use the
  equivalent `(LeafAdopt.abVarEquiv K).symm (PkgI3.AbVar.zero K)` (defeq to the copy body).
- Zero-AV proofs (`trivModel.gen_hom`, `bcUnitIso`, `semistableNeronIdentityComponent_zero`) unfold
  `(AbVar.zero K).baseChange L` through `ZInQ.DefFaltings.AbVar.baseChange`. The body is identical
  to PkgI3's, so this should be fine.
- `isMonHom_prodComparisonIso` / `productGroupModelExists` are instance-heavy, but they do not mention
  `AbVar` copies beyond `A.X`, so they should behave as in the kernel.
- `open scoped Obj` (ProductProof section) as in the source.
- The bridge `heightAdditivity_unfolded` is new and uncompiled; the likeliest fix point is the
  `rw [asIso_hom, CartesianMonoidalCategory.lift_fst]` (fall back to `simpa using h₁`).
