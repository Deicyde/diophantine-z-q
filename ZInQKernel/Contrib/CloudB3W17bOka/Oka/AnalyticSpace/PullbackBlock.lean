/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.PullbackOpen

/-!
# The transition data of a fibre product glued over a family of opens

`Mathlib/AlgebraicGeometry/Pullbacks.lean` builds the fibre product of schemes by gluing the
pullbacks `Uᵢ ×_Z Y` taken over the members of an affine cover of `X`. The transition data of that
gluing — the overlaps `v i j`, the swap `t i j` between `v i j` and `v j i`, the induced map `t'`
on triple overlaps, and the cocycle law `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙` — is a block of
declarations that mentions no scheme theory at all: it is bookkeeping about pullbacks in a
category, and the only thing it asks of that category is that the pullbacks it names exist.

**This file is that block for `ComplexAnalytic.AnalyticSpace`, together with what the consumer of
the block needs and the block does not supply.**

## The consumer, and why it decides the shape of this file

`Oka/AnalyticSpace/Glue.lean`'s entry points, `ComplexAnalytic.AnalyticSpace.ofGlueData` and
`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear`, take an
`AlgebraicGeometry.LocallyRingedSpace.GlueData`, and that file's header records the absence of a
glue datum over `ComplexAnalytic.AnalyticSpace` as a decision rather than as an oversight. So a
`t'` stated over `ComplexAnalytic.AnalyticSpace` — which is what transcribes for free — is not the
`t'` that datum wants: its `t'` is a morphism between pullbacks taken in
`AlgebraicGeometry.LocallyRingedSpace`, and those are different objects.

**The whole content of the second half of this file is that they differ by an isomorphism, and
that the isomorphism is already in the tree.**
`ComplexAnalytic.AnalyticSpace.isPullback_map_pullback_pullbackFst_ofRestrict` says that
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` carries the analytic pullback square at
a cospan of two `CategoryTheory.Limits.pullback.fst`s at open-subspace inclusions to a pullback
square, and the cospan of `ComplexAnalytic.AnalyticSpace.Pullback.fV i j` and
`ComplexAnalytic.AnalyticSpace.Pullback.fV i k` is exactly of that shape. Reading that square as a
`CategoryTheory.IsPullback.isoPullback` gives
`ComplexAnalytic.AnalyticSpace.Pullback.isoPullbackFV`, and
`ComplexAnalytic.AnalyticSpace.Pullback.t'Map` is the analytic `t'` **conjugated** by it.

Nothing downstairs is reproved. The cocycle law downstairs,
`ComplexAnalytic.AnalyticSpace.Pullback.t'Map_cocycle`, is the analytic one with the conjugating
isomorphisms cancelled, and it mentions none of the six `cocycle_*` lemmas the analytic cocycle is
proved from.

## What is hypothesised rather than derived, and why

The ambient limits `Uᵢ ×_Z Y` enter as `[∀ i, CategoryTheory.Limits.HasPullback
(X.ofRestrict (U i) ≫ f) g]` and not from any instance of this repository. That is Mathlib's own
shape — its block quantifies over a scheme cover and takes the ambient pullbacks as given — and
here it also keeps the file's import to `Oka/AnalyticSpace/PullbackOpen.lean` alone. A caller
supplies the hypothesis from wherever it has one; `Oka/AnalyticSpace/CutOutFibreProduct.lean`'s
`ComplexAnalytic.AnalyticSpace.hasPullback_ofCutOut` is one such source, at a cospan of local
models presented by cut-out data, and **no declaration of this file is stated about that cospan or
about any other property of those limits.**

**The index is a family of opens and not a cover.** No declaration below asks the `U i` to cover
`X`: the block is bookkeeping about overlaps and is true of any family. Joint surjectivity is what
the *glue* needs — the glued object, its two projections and the proof that it is the fibre
product — and none of that is here. There is still no `structure OpenCover` over
`ComplexAnalytic.AnalyticSpace` in this repository, and this file does not introduce one, because
the block gives no reason to choose between reusing
`AlgebraicGeometry.LocallyRingedSpace.OpenCover` and bundling an analytic one.

**Every member map is syntactically an `ComplexAnalytic.AnalyticSpace.ofRestrict`, and after
`Oka/AnalyticSpace/PullbackOpen.lean` that is load-bearing rather than tidy**: both
`ComplexAnalytic.AnalyticSpace.isOpenImmersion_map_pullbackFst_ofRestrict` and
`ComplexAnalytic.AnalyticSpace.isPullback_map_pullback_pullbackFst_ofRestrict` are keyed on that
spelling, and a member map given as a general open immersion would be reached by neither.

## Main results

- `ComplexAnalytic.AnalyticSpace.Pullback.v`, `ComplexAnalytic.AnalyticSpace.Pullback.t`,
  `ComplexAnalytic.AnalyticSpace.Pullback.fV` and `ComplexAnalytic.AnalyticSpace.Pullback.t'`:
  **Mathlib's transition data, transcribed**, with the three `t_*` factorisation lemmas,
  `ComplexAnalytic.AnalyticSpace.Pullback.t_id`, the six `t'_*` factorisation lemmas and the six
  `cocycle_*` lemmas that go with them.
- `ComplexAnalytic.AnalyticSpace.Pullback.cocycle`: **the cocycle law upstairs**.
- `ComplexAnalytic.AnalyticSpace.Pullback.isOpenImmersion_map_fV`: the image of a member map of the
  overlap datum is an open immersion of locally ringed spaces, which is the instance that lets the
  pullbacks below be taken there at all.
- `ComplexAnalytic.AnalyticSpace.Pullback.isoPullbackFV`: **the image of the analytic triple
  overlap *is* the locally-ringed-space pullback of the two member maps.**
- `ComplexAnalytic.AnalyticSpace.Pullback.t'Map` and
  `ComplexAnalytic.AnalyticSpace.Pullback.t'Map_cocycle`: **the transition map and its cocycle law
  in the category `AlgebraicGeometry.LocallyRingedSpace.GlueData` is stated over**, obtained from
  the analytic ones by conjugation and by nothing else.
- `ComplexAnalytic.AnalyticSpace.Pullback.t'Map_snd`: what the second projection of that map is,
  which is the factorisation a glue datum's `t_fac` field is stated in terms of.

## What this does not do

**It does not build an `AlgebraicGeometry.LocallyRingedSpace.GlueData` and it does not make
`ComplexAnalytic.AnalyticSpace` a category with pullbacks.** The remaining fields of Mathlib's
`gluing` — `f_mono`, `f_id` and `t_fac` — and everything after it — `p1`, `p2`, `gluedLift`,
`pullbackP1Iso`, `gluedIsLimit` and `hasPullback_of_cover` — are not here.
`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` does not synthesise at the
commit that adds this file, and no declaration below claims otherwise.

**It says nothing about the ambient cospan.** The comparison this file supplies is at the cospan
of two member maps of the overlap datum, both of which are `CategoryTheory.Limits.pullback.fst` at
an open-subspace inclusion. Whether the analytic `Uᵢ ×_Z Y` is the locally-ringed-space pullback of
`X.ofRestrict (U i) ≫ f` and `g` is a different question, at a cospan neither of whose legs is an
`ComplexAnalytic.AnalyticSpace.ofRestrict`, and **no declaration of this file bears on it**. That
this file does not need an answer is the reason its transition data is stated with the analytic
objects rather than with locally-ringed-space ones.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace ComplexAnalytic.AnalyticSpace.Pullback

variable {X Y Z : AnalyticSpace.{u}} {I : Type u} (U : I → X.Opens) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [∀ i, HasPullback (X.ofRestrict (U i) ≫ f) g]

/-! ### The overlaps and the swap between them

Mathlib's `AlgebraicGeometry.Scheme.Pullback.v`, `t` and the three factorisation lemmas for `t`,
with `𝒰.f i` replaced by `ComplexAnalytic.AnalyticSpace.ofRestrict` at the `i`-th member of the
family. The proofs are Mathlib's `simp only` argument lists unchanged: the block is bookkeeping
about pullbacks in a category and nothing in it is about schemes. -/

/-- **The overlap `(Uᵢ ×_Z Y) ×_X Uⱼ`.**

`@[implicit_reducible]` for the reason Mathlib's copy carries it:
`ComplexAnalytic.AnalyticSpace.Pullback.t'` and the six `t'_*` lemmas state morphisms out of
pullbacks *of* this object's projections, and instance search has to see through the definition to
find the pullbacks those mention. -/
@[implicit_reducible]
noncomputable def v (i j : I) : AnalyticSpace.{u} :=
  pullback ((pullback.fst (X.ofRestrict (U i) ≫ f) g) ≫ X.ofRestrict (U i)) (X.ofRestrict (U j))

/-- **The swap `(Uᵢ ×_Z Y) ×_X Uⱼ ⟶ (Uⱼ ×_Z Y) ×_X Uᵢ`.**

The two `CategoryTheory.Limits.hasPullback_assoc_symm` hypotheses are what make the two
`CategoryTheory.Limits.pullbackAssoc` isomorphisms in the proof elaborate; they are stated as
`have`s rather than as instances of this file because they are about a reassociation of the
particular cospan below and not about a shape the category should be told to have. -/
noncomputable def t (i j : I) : v U f g i j ⟶ v U f g j i := by
  have : HasPullback (pullback.snd _ _ ≫ X.ofRestrict (U i) ≫ f) g :=
    hasPullback_assoc_symm (X.ofRestrict (U j)) (X.ofRestrict (U i)) (X.ofRestrict (U i) ≫ f) g
  have : HasPullback (pullback.snd _ _ ≫ X.ofRestrict (U j) ≫ f) g :=
    hasPullback_assoc_symm (X.ofRestrict (U i)) (X.ofRestrict (U j)) (X.ofRestrict (U j) ≫ f) g
  refine (pullbackSymmetry ..).hom ≫ (pullbackAssoc ..).inv ≫ ?_
  refine ?_ ≫ (pullbackAssoc ..).hom ≫ (pullbackSymmetry ..).hom
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · rw [pullbackSymmetry_hom_comp_snd_assoc, pullback.condition_assoc, Category.comp_id]
  · rw [Category.comp_id, Category.id_comp]

@[simp, reassoc]
theorem t_fst_fst (i j : I) : t U f g i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
    pullback.snd _ _ := by
  simp only [t, Category.assoc, pullbackSymmetry_hom_comp_fst_assoc, pullbackAssoc_hom_snd_fst,
    pullback.lift_fst_assoc, pullbackSymmetry_hom_comp_snd, pullbackAssoc_inv_fst_fst,
    pullbackSymmetry_hom_comp_fst]

@[simp, reassoc]
theorem t_fst_snd (i j : I) :
    t U f g i j ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t, Category.assoc, pullbackSymmetry_hom_comp_fst_assoc, pullbackAssoc_hom_snd_snd,
    pullback.lift_snd, Category.comp_id, pullbackAssoc_inv_snd, pullbackSymmetry_hom_comp_snd_assoc]

@[simp, reassoc]
theorem t_snd (i j : I) : t U f g i j ≫ pullback.snd _ _ =
    pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [t, Category.assoc, pullbackSymmetry_hom_comp_snd, pullbackAssoc_hom_fst,
    pullback.lift_fst_assoc, pullbackSymmetry_hom_comp_fst, pullbackAssoc_inv_fst_snd,
    pullbackSymmetry_hom_comp_snd_assoc]

theorem t_id (i : I) : t U f g i i = 𝟙 _ := by
  apply pullback.hom_ext <;> rw [Category.id_comp]
  · apply pullback.hom_ext
    · rw [← cancel_mono (X.ofRestrict (U i))]
      simp only [pullback.condition, Category.assoc, t_fst_fst]
    · simp only [Category.assoc, t_fst_snd]
  · rw [← cancel_mono (X.ofRestrict (U i))]; simp only [pullback.condition, t_snd, Category.assoc]

/-! ### The transition map on triple overlaps, and the cocycle law

Mathlib's `AlgebraicGeometry.Scheme.Pullback.fV`, `t'`, the six `t'_*` factorisation lemmas and the
six `cocycle_*` lemmas, transcribed the same way. `fV` is kept as an `abbrev`, which is what makes
the pullbacks in `t'`'s statement elaborate without unfolding it by hand. -/

/-- **The inclusion of the overlap into the `i`-th piece.**

An `abbrev` rather than a `def`, as Mathlib's is: it appears inside the pullbacks that `t'`'s
*type* names, so it has to reduce during elaboration of that type, where no `haveI` is reachable.
It is the leg that
`ComplexAnalytic.AnalyticSpace.Pullback.isOpenImmersion_map_fV` and
`ComplexAnalytic.AnalyticSpace.Pullback.isoPullbackFV` are stated at, and it is a
`CategoryTheory.Limits.pullback.fst` at an `ComplexAnalytic.AnalyticSpace.ofRestrict`. -/
noncomputable abbrev fV (i j : I) : v U f g i j ⟶ pullback (X.ofRestrict (U i) ≫ f) g :=
  pullback.fst _ _

/-- **The transition map on triple overlaps**, `((Uᵢ ×_Z Y) ×_X Uⱼ) ×_{Uᵢ ×_Z Y} ((Uᵢ ×_Z Y) ×_X Uₖ)
⟶ ((Uⱼ ×_Z Y) ×_X Uₖ) ×_{Uⱼ ×_Z Y} ((Uⱼ ×_Z Y) ×_X Uᵢ)`.

Mathlib's construction, unchanged: two `CategoryTheory.Limits.pullbackRightPullbackFstIso`
isomorphisms with `ComplexAnalytic.AnalyticSpace.Pullback.t` mapped across in between. -/
noncomputable def t' (i j k : I) :
    pullback (fV U f g i j) (fV U f g i k) ⟶ pullback (fV U f g j k) (fV U f g j i) := by
  refine (pullbackRightPullbackFstIso ..).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso ..).inv
  refine pullback.map _ _ _ _ (t U f g i j) (𝟙 _) (𝟙 _) ?_ ?_
  · simp_rw [Category.comp_id, t_fst_fst_assoc, ← pullback.condition]
  · rw [Category.comp_id, Category.id_comp]

@[simp, reassoc]
theorem t'_fst_fst_fst (i j k : I) :
    t' U f g i j k ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.lift_fst_assoc, t_fst_fst,
    pullbackRightPullbackFstIso_hom_fst_assoc]

@[simp, reassoc]
theorem t'_fst_fst_snd (i j k : I) :
    t' U f g i j k ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_fst_assoc, pullback.lift_fst_assoc, t_fst_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]

@[simp, reassoc]
theorem t'_fst_snd (i j k : I) :
    t' U f g i j k ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_snd, pullback.lift_snd, Category.comp_id,
    pullbackRightPullbackFstIso_hom_snd]

@[simp, reassoc]
theorem t'_snd_fst_fst (i j k : I) :
    t' U f g i j k ≫ pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_fst_fst,
    pullbackRightPullbackFstIso_hom_fst_assoc]

@[simp, reassoc]
theorem t'_snd_fst_snd (i j k : I) :
    t' U f g i j k ≫ pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_fst_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]

@[simp, reassoc]
theorem t'_snd_snd (i j k : I) :
    t' U f g i j k ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [t', Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    pullbackRightPullbackFstIso_inv_fst_assoc, pullback.lift_fst_assoc, t_snd,
    pullbackRightPullbackFstIso_hom_fst_assoc]

theorem cocycle_fst_fst_fst (i j k : I) :
    t' U f g i j k ≫ t' U f g j k i ≫ t' U f g k i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫
      pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [t'_fst_fst_fst, t'_fst_snd, t'_snd_snd]

theorem cocycle_fst_fst_snd (i j k : I) :
    t' U f g i j k ≫ t' U f g j k i ≫ t' U f g k i j ≫ pullback.fst _ _ ≫ pullback.fst _ _ ≫
      pullback.snd _ _ = pullback.fst _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t'_fst_fst_snd]

theorem cocycle_fst_snd (i j k : I) :
    t' U f g i j k ≫ t' U f g j k i ≫ t' U f g k i j ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [t'_fst_snd, t'_snd_snd, t'_fst_fst_fst]

theorem cocycle_snd_fst_fst (i j k : I) :
    t' U f g i j k ≫ t' U f g j k i ≫ t' U f g k i j ≫ pullback.snd _ _ ≫ pullback.fst _ _ ≫
      pullback.fst _ _ = pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.fst _ _ := by
  simp only [pullback.condition_assoc, t'_snd_fst_fst, t'_fst_snd, t'_snd_snd]

theorem cocycle_snd_fst_snd (i j k : I) :
    t' U f g i j k ≫ t' U f g j k i ≫ t' U f g k i j ≫ pullback.snd _ _ ≫ pullback.fst _ _ ≫
      pullback.snd _ _ = pullback.snd _ _ ≫ pullback.fst _ _ ≫ pullback.snd _ _ := by
  simp only [pullback.condition_assoc, t'_snd_fst_snd]

theorem cocycle_snd_snd (i j k : I) :
    t' U f g i j k ≫ t' U f g j k i ≫ t' U f g k i j ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  simp only [t'_snd_snd, t'_fst_fst_fst, t'_fst_snd]

/-- **The cocycle law.** Mathlib's proof, which is the six `cocycle_*` lemmas fed to five nested
applications of `CategoryTheory.Limits.pullback.hom_ext`; its comment records that `tidy` should
close it and times out. -/
theorem cocycle (i j k : I) : t' U f g i j k ≫ t' U f g j k i ≫ t' U f g k i j = 𝟙 _ := by
  apply pullback.hom_ext <;> rw [Category.id_comp]
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp_rw [Category.assoc, cocycle_fst_fst_fst U f g i j k]
      · simp_rw [Category.assoc, cocycle_fst_fst_snd U f g i j k]
    · simp_rw [Category.assoc, cocycle_fst_snd U f g i j k]
  · apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp_rw [Category.assoc, cocycle_snd_fst_fst U f g i j k]
      · simp_rw [Category.assoc, cocycle_snd_fst_snd U f g i j k]
    · simp_rw [Category.assoc, cocycle_snd_snd U f g i j k]

/-! ### The same transition map in the category a glue datum is stated over

Everything above is a statement about pullbacks taken in `ComplexAnalytic.AnalyticSpace`. A
`AlgebraicGeometry.LocallyRingedSpace.GlueData`'s `t'` is a morphism between pullbacks taken in
`AlgebraicGeometry.LocallyRingedSpace`, which are different objects, and the six declarations
below are the whole of the difference. -/

/-- **The morphism `Uᵢ ×_Z Y ⟶ X` the overlap is a pullback along.**

Named because it is the `f` argument of the two `Oka/AnalyticSpace/PullbackOpen.lean` declarations
this section applies, and reading `ComplexAnalytic.AnalyticSpace.Pullback.fV` as a
`CategoryTheory.Limits.pullback.fst` **at this morphism** and at
`ComplexAnalytic.AnalyticSpace.ofRestrict` is what makes them apply at all. -/
noncomputable abbrev toBase (i : I) : pullback (X.ofRestrict (U i) ≫ f) g ⟶ X :=
  pullback.fst (X.ofRestrict (U i) ≫ f) g ≫ X.ofRestrict (U i)

/-- **The image of a member map of the overlap datum is an open immersion of locally ringed
spaces.**

`ComplexAnalytic.AnalyticSpace.isOpenImmersion_map_pullbackFst_ofRestrict` at
`ComplexAnalytic.AnalyticSpace.Pullback.toBase`, and that theorem's docstring prescribes exactly
this: it is stated as a theorem rather than as an instance so that a caller ascribes it at the
spelling its own goal uses, and this is the caller. **Stated as an instance here and not as a
theorem**, because the pullbacks in the types of
`ComplexAnalytic.AnalyticSpace.Pullback.isoPullbackFV` and
`ComplexAnalytic.AnalyticSpace.Pullback.t'Map` are what it has to be found for, and a type is
elaborated where no call-site ascription is reachable. -/
instance isOpenImmersion_map_fV (i j : I) :
    LocallyRingedSpace.IsOpenImmersion (forgetToLocallyRingedSpace.map (fV U f g i j)) :=
  isOpenImmersion_map_pullbackFst_ofRestrict (toBase U f g i) (U j)

/-- **The image of the analytic triple overlap *is* the locally-ringed-space pullback of the two
member maps.**

`ComplexAnalytic.AnalyticSpace.isPullback_map_pullback_pullbackFst_ofRestrict` at
`ComplexAnalytic.AnalyticSpace.Pullback.toBase` and the two opens, read as an isomorphism. **The
functor is not known to preserve any limit** — it is faithful and not full, and the paragraph on
`ComplexAnalytic.AnalyticSpace.isPullback_map_ofRestrict` says why that cannot be assumed away —
so this is not an instance of a general fact about it, it is that one theorem at this cospan. -/
noncomputable def isoPullbackFV (i j k : I) :
    forgetToLocallyRingedSpace.obj (pullback (fV U f g i j) (fV U f g i k)) ≅
      pullback (forgetToLocallyRingedSpace.map (fV U f g i j))
        (forgetToLocallyRingedSpace.map (fV U f g i k)) :=
  (isPullback_map_pullback_pullbackFst_ofRestrict (toBase U f g i) (U j) (U k)).isoPullback

/-- **The transition map on triple overlaps, in the category a glue datum is stated over.**

The analytic `ComplexAnalytic.AnalyticSpace.Pullback.t'` conjugated by
`ComplexAnalytic.AnalyticSpace.Pullback.isoPullbackFV` at each end, and nothing else: no square is
reproved downstairs and no property of
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` beyond functoriality is used. **This is
the shape `AlgebraicGeometry.LocallyRingedSpace.GlueData`'s `t'` field has**, with the datum's
objects taken to be the images of the analytic ones. -/
noncomputable def t'Map (i j k : I) :
    pullback (forgetToLocallyRingedSpace.map (fV U f g i j))
        (forgetToLocallyRingedSpace.map (fV U f g i k)) ⟶
      pullback (forgetToLocallyRingedSpace.map (fV U f g j k))
        (forgetToLocallyRingedSpace.map (fV U f g j i)) :=
  (isoPullbackFV U f g i j k).inv ≫ forgetToLocallyRingedSpace.map (t' U f g i j k) ≫
    (isoPullbackFV U f g j k i).hom

/-- **The cocycle law downstairs**, which is
`ComplexAnalytic.AnalyticSpace.Pullback.cocycle` with the conjugating isomorphisms cancelled.

It mentions none of the six `cocycle_*` lemmas the analytic one is proved from, and that is the
point of stating the datum's objects analytically: a law downstairs is the law upstairs
transported, so the six `t'_*` and six `cocycle_*` lemmas are proved once and not twice. -/
theorem t'Map_cocycle (i j k : I) :
    t'Map U f g i j k ≫ t'Map U f g j k i ≫ t'Map U f g k i j = 𝟙 _ := by
  simp only [t'Map, Category.assoc, Iso.hom_inv_id_assoc,
    ← forgetToLocallyRingedSpace.map_comp_assoc, cocycle]
  rw [forgetToLocallyRingedSpace.map_id, Category.id_comp, Iso.inv_hom_id]

/-- **The second projection of the transition map downstairs**, which is the analytic second
projection carried down and precomposed with one conjugating isomorphism.

`AlgebraicGeometry.LocallyRingedSpace.GlueData`'s `t_fac` field is an equation between
`t' i j k ≫ pullback.snd _ _` and `pullback.fst _ _ ≫ t i j`, so this is the side of that equation
which the conjugation touches; the other side is untouched. **Discharging `t_fac` itself is not
done here** — it needs the analytic factorisation of
`ComplexAnalytic.AnalyticSpace.Pullback.t'` through
`ComplexAnalytic.AnalyticSpace.Pullback.t`, which is a statement about the datum rather than about
the block. -/
theorem t'Map_snd (i j k : I) :
    t'Map U f g i j k ≫ pullback.snd _ _ =
      (isoPullbackFV U f g i j k).inv ≫
        forgetToLocallyRingedSpace.map (t' U f g i j k ≫ pullback.snd _ _) := by
  simp only [t'Map, Category.assoc, Functor.map_comp, isoPullbackFV,
    IsPullback.isoPullback_hom_snd]

end ComplexAnalytic.AnalyticSpace.Pullback
