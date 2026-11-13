# morph-descend: G4's input `MorphismsDescend` (EGA IV₃ 8.8.2) is proved

## Main result

**`MorphismsDescend` is now a theorem, so it is no longer a leaf.** It is the input of
`scratch/g4-weilres/G4.lean` (`docs/research/g4-weilres.md`) that spreads morphisms out over
`ℚ̄ = colim L`, following EGA IV₃ 8.8.2. The proof uses no hypotheses, no `sorry`, and only the
standard axioms.

- **Headline:** `MorphDescend.morphismsDescend : MorphDescend.MorphismsDescend` in
  `scratch/morph-descend/Descend.lean` (404 lines).
  - The statement and its auxiliary definitions (`specEmb`, `specIncl`, `specEmb_factor`, `cmpL`)
    are copied verbatim from G4.lean. VERIFIED: the two blocks are textually identical under
    `diff`.
  - It compiles with 0 errors and 0 warnings.
  - VERIFIED by `#print axioms` for both `exists_descend` and `morphismsDescend`: they depend on
    `[propext, Classical.choice, Quot.sound]` only.
- **G4 with the input removed:** `scratch/morph-descend/G4Closed.lean` (1903 lines) has three
  parts, in order:
  1. the `MorphDescend` block;
  2. G4.lean, unchanged;
  3. three new theorems:
     - `G4WeilRes.morphismsDescend : G4WeilRes.MorphismsDescend`, whose proof term is
       `MorphDescend.morphismsDescend`. G4's `Qbar` is `GlueB3Unram.Qbar` and ours is
       `MorphDescend.Qbar`; both are the reducible abbreviation `AlgebraicClosure ℚ`, and
       elaboration identifies them.
     - `G4WeilRes.homDescends : HomDescends`, which makes the continuity input unconditional.
     - `G4WeilRes.homField_of_model_closed`: the G4 headline `homField_of_model_leaves` without
       its `hM : MorphismsDescend` argument.

  It compiles with no errors. VERIFIED: every printed theorem depends only on the standard
  axioms.

**G4's inputs after this task:**

- the leaf `PkgI3.HomFreeFinite`;
- `InertiaFixesHoms`;
- the hypotheses `hK` (G2), `hgood` (G3) and `hdim`.

## 1. What Mathlib has (VERIFIED by reading `.lake/packages/mathlib`, v4.35.0)

All of these are in `Mathlib/AlgebraicGeometry/AffineTransitionLimit.lean`.

- **`Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`** (around line 1222):
  - Setting: a cofiltered diagram `D : I ⥤ Scheme` with affine transition maps and qcqs terms, a
    limit cone `c`, and `f : X → S` locally of finite presentation.
  - Statement: every `S`-morphism `a : c.pt → X` factors as `c.π_i ≫ g` for some `i` and some
    `S`-morphism `g : D_i → X`.
  - This is the surjectivity half of Stacks 01ZC (1)⇒(3), the form of EGA IV₃ 8.8.2(ii) that is
    needed. STANDARD; EGA numbering UNVERIFIED. The lemma has no Stacks tag in Mathlib, but its
    injective companion carries `@[stacks 01ZC "Injective part of (1) => (3)"]`.
- `Scheme.exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`: the injective half, which is not
  needed here.
- `Scheme.preservesColimit_yoneda`: both halves packaged as preservation of the filtered colimit by
  `Hom_S(-, X)`.

So the deep part, spreading out, is already in Mathlib. What was missing was the glue that
presents `A ×_{K,e} ℚ̄` as such a limit. That glue is proved here.

## 2. The proof (all in `Descend.lean`, all compiled)

| Declaration | Content |
| --- | --- |
| `Idx E₀` | the finite subextensions `E₀ ⊆ L ⊆ ℚ̄`, a directed order, nonempty when `[E₀:ℚ] < ∞` |
| `ringCoconeIsColimit` | `ℚ̄ = colim L` in `CommRingCat`, by reflecting a filtered colimit of types (`Types.FilteredColimit.isColimitOf'`) through `forget CommRingCat`; each `x` lies in `E₀ ⊔ ℚ(x)` |
| `specConeIsLimit` | `Spec ℚ̄ = lim Spec L` in `Over (Spec K)`. `Scheme.Spec` preserves limits (it is a right adjoint), and `Over.forget` reflects connected limits |
| `bcConeIsLimit` | `X ×_K ℚ̄ = lim (L ×_K X)` in `Scheme`. `Over.pullback X.hom` is a right adjoint and `Over.forget` preserves connected limits. The diagram `bcDiag` and cone `bcCone` are written with explicit `pullback`/`pullback.lift`, so they are syntactically usable |
| `bcDiag_isAffineHom` | the transition maps are base changes of `Spec L' → Spec L` (`IsPullback.of_right`), hence affine |
| `bcDiag_compactSpace`, `bcDiag_quasiSeparatedSpace` | the terms are qcqs when `X → Spec K` is qcqs |
| `exists_descend` | the general statement (below) |
| `morphismsDescend` | the instance for `PkgI3.AbVar`, with `E₀ = e₁(K) ⊔ e₂(K)` |

**`exists_descend` (general form, compiled).** The hypotheses are:

- `K` is any field, and `X, Y : Over (Spec K)`;
- `X → Spec K` is quasi-compact and quasi-separated;
- `Y → Spec K` is locally of finite presentation;
- `e₁, e₂ : K →+* ℚ̄` have image in a number field `E₀`.

Conclusion: every `ℚ̄`-morphism `φ : X ×_{K,e₁} ℚ̄ → Y ×_{K,e₂} ℚ̄` satisfies
`φ ≫ cmp = cmp ≫ ψ`, for some number field `E₀ ⊆ L ⊆ ℚ̄` and some
`ψ : X ×_{K,e₁|L} L → Y ×_{K,e₂|L} L`.

The proof applies Mathlib's lemma to:

- the diagram `D = bcDiag` (the base changes of `X` along `e₁|L`);
- the structure maps `t_L : D_L → Spec L → Spec K`, via `e₂|L`;
- the morphism `a = φ ≫ pr_Y : X ×_{e₁} ℚ̄ → Y`.

This gives `g : D_L → Y` over `K`, and `ψ = (g, pr_L)`.

**What the instance uses about `AbVar`.** Only two properties are used: proper ⇒ quasi-compact
and quasi-separated for `A`, and smooth ⇒ locally of finite presentation for `B`. The group
structure is not used, and `φ` is an arbitrary `ℚ̄`-morphism.

## 3. Status for integration

- `MorphismsDescend` should move from "inputs" to "glue, proved" in `docs/research/g4-weilres.md`
  and in `docs/research/h-decomposition.md`. G4.lean listed it as a "leaf candidate (EGA IV₃
  8.8.2)".
- Integration options: G4Closed.lean can replace G4.lean, or `Descend.lean` can be prepended to
  it. The new declarations only depend on Mathlib and `ZInQKernel.HDecomp.Objects`.
- Not done: the injectivity half of 8.8.2 (uniqueness of `ψ` up to enlarging `L`). G4 does not
  use it, and Mathlib has it as well (`exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType`).
