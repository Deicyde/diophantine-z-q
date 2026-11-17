/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.Glue
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.PullbackBlock

/-!
# The fibre product glued out of a family of opens, and its two projections

`Oka/AnalyticSpace/PullbackBlock.lean` builds the transition data of the gluing that
`Mathlib/AlgebraicGeometry/Pullbacks.lean` uses to make a fibre product of schemes — the overlaps
`ComplexAnalytic.AnalyticSpace.Pullback.v`, the swap
`ComplexAnalytic.AnalyticSpace.Pullback.t`, the triple-overlap map
`ComplexAnalytic.AnalyticSpace.Pullback.t'` and the cocycle law — and stops there. Its own
docstring says what it does not do: *"It does not build an
`AlgebraicGeometry.LocallyRingedSpace.GlueData` and it does not make
`ComplexAnalytic.AnalyticSpace` a category with pullbacks."*

**This file does the first of those two.** It assembles the block into an
`AlgebraicGeometry.LocallyRingedSpace.GlueData`, promotes the gluing to a complex analytic space
through `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear`, and produces the two projections and
the square they make commute. **It does not do the second**, and the last section below says
exactly what is still missing.

## Why the datum is stated one category down

`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` takes an
`AlgebraicGeometry.LocallyRingedSpace.GlueData`, and **this repository declares no glue-datum type
— not over `ComplexAnalytic.AnalyticSpace` and not over anything else — while every glue datum it
builds is a term of one of Mathlib's.** Both halves are one walk of the environment at `487ea43`,
over the declarations whose declaring module begins `Oka`, taking the head of the codomain under
`Lean.Meta.forallTelescopeReducing`: of the **sixteen** inductive types declared, not one is a glue
datum, and of the declarations whose codomain is one, **thirteen** are under `Oka/` — ten into
`AlgebraicGeometry.LocallyRingedSpace.GlueData`, this file's own
`ComplexAnalytic.AnalyticSpace.Pullback.gluing` among them, and three into
`CategoryTheory.GlueData'`.
`ComplexAnalytic.GlueDataCLinear` is a `def` into `Prop` **on** a locally-ringed-space datum and
not a datum of its own.

**The instrument is the codomain and not the name**, because a `GlueData` in a declaration's name
says nothing about what that declaration is. `scripts/DumpOkaDecls.lean` at `487ea43` attributes
**seventy-five** names containing `GlueData` to modules under `Oka/`, spread over fourteen of
them — twenty in `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean`, twelve in
`Oka/AnalyticSpace/Glue.lean`, eleven in
`Oka/Geometry/RingedSpace/PresheafedSpace/Double.lean` and ten in
`Oka/CategoryTheory/GlueData.lean`, which is named for a glue datum and declares ten theorems and
no type — and every one of the seventy-five is a theorem or a definition. Which of them *build* a
datum, and into which type, is a question about codomains, and that is the question
`Lean.Meta.forallTelescopeReducing` was pointed at. So the datum here has
`AlgebraicGeometry.LocallyRingedSpace` objects and morphisms throughout, and every field of it is
the image under `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` of something the block
already built:

* `U` and `V` are the images of the ambient pullbacks and of
  `ComplexAnalytic.AnalyticSpace.Pullback.v`;
* `f` is the image of `ComplexAnalytic.AnalyticSpace.Pullback.fV`, and its `f_open` field is
  `ComplexAnalytic.AnalyticSpace.Pullback.isOpenImmersion_map_fV`. That is stated as an instance
  there, though **not for this field** — its own docstring gives the reason as the elaboration of
  `ComplexAnalytic.AnalyticSpace.Pullback.isoPullbackFV`'s and `…t'Map`'s types — and the field
  takes it either way;
* `t` is the image of `ComplexAnalytic.AnalyticSpace.Pullback.t`, and `t_id` is
  `ComplexAnalytic.AnalyticSpace.Pullback.t_id` carried across by
  `CategoryTheory.Functor.map_id`;
* `t'` is `ComplexAnalytic.AnalyticSpace.Pullback.t'Map` **on the nose** and `cocycle` is
  `ComplexAnalytic.AnalyticSpace.Pullback.t'Map_cocycle` **on the nose**. The datum's `t'` field
  has type `pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)` in
  `AlgebraicGeometry.LocallyRingedSpace`, and that is the type `…t'Map` was given; nothing is
  transported here that was not transported there.

**Three fields are supplied by neither the block nor a projection of it, and instance search
finds all three**: `f_mono` and `f_hasPullback` from `f_open`, and `f_id` from
`CategoryTheory.Functor.map_isIso` applied to an isomorphism instance search already finds
upstairs. The remaining field is `t_fac`, and it is the subject of the next section.

## The one field that needed a lemma, and where it splits

`t_fac` — `t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j` — is the only field that is
neither a projection of the block nor an instance. Mathlib proves its analogue inline inside
`gluing`; here it splits in two, and the split is the point:

* `ComplexAnalytic.AnalyticSpace.Pullback.t'_fac` is that equation **upstairs**, between morphisms
  of analytic spaces, and its proof is Mathlib's inline one unchanged — two
  `CategoryTheory.Limits.pullback.hom_ext`s and the same six factorisation lemmas, three for
  `ComplexAnalytic.AnalyticSpace.Pullback.t'` and three for `…t`.
* `ComplexAnalytic.AnalyticSpace.Pullback.t'Map_fac` carries it down, and it is where the
  conjugation is discharged. `…t'Map_snd` rewrites the left-hand side into
  `…isoPullbackFV`'s inverse followed by the image of the analytic composite; `t'_fac` rewrites
  that composite; and what remains is `CategoryTheory.IsPullback.isoPullback_inv_fst`, which
  cancels the surviving conjugation against the pullback projection it was built from.

**So the datum owes no new mathematics about pullbacks and one lemma about the comparison**, and
that is the shape `Oka/AnalyticSpace/PullbackBlock.lean` predicted when it said its `t'Map_snd`
is *"the side of that equation which the conjugation touches; the other side is untouched"*.

## The projections, and why they are glued rather than descended

`ComplexAnalytic.AnalyticSpace.Pullback.p1` and `…p2` are
`ComplexAnalytic.AnalyticSpace.glueMorphismsOfGlueData` at the families
`ComplexAnalytic.AnalyticSpace.Pullback.toBase` and `CategoryTheory.Limits.pullback.snd`. Mathlib
builds its `p1` and `p2` by `CategoryTheory.Limits.Multicoequalizer.desc` on the datum's diagram
instead; both routes exist here, and `…glueMorphismsOfGlueData` is taken because it returns a
**morphism of analytic spaces** rather than a morphism of locally ringed spaces. Its two
hypotheses are discharged from the block: the compatibility from
`ComplexAnalytic.AnalyticSpace.Pullback.fV_comp_toBase`, which is
`ComplexAnalytic.AnalyticSpace.Pullback.t_fst_fst` together with
`CategoryTheory.Limits.pullback.condition` at the overlap, and `…fV_comp_snd`, which is
`ComplexAnalytic.AnalyticSpace.Pullback.t_fst_snd` alone; and the `ℂ`-linearity from the
`isCLinear` field the morphisms carry.

**The `ℂ`-linearity of the datum is free for the same reason.**
`ComplexAnalytic.GlueDataCLinear` is supplied by `ComplexAnalytic.glueDataCLinear_of_isCLinearHom`
from linearity of the legs and of the transitions, and both are field projections of analytic
morphisms — `ComplexAnalytic.AnalyticSpace.Hom` carries `ComplexAnalytic.IsCLinearHom` in a field.
This is the use `Oka/AnalyticSpace/Glue.lean` states that lemma for.

## Where the covering hypothesis enters, and it is one declaration deep

**Everything through `ComplexAnalytic.AnalyticSpace.Pullback.overlapLift_t_fV` is about an
arbitrary family of opens** — that much is inherited from
`Oka/AnalyticSpace/PullbackBlock.lean` rather than decided here, since the gluing of a family of
opens is an analytic space whatever the family is.

**From `ComplexAnalytic.AnalyticSpace.Pullback.conePreimage_covers` on, the `U i` are asked to
cover `X`**, as the hypothesis `hU`. A lift out of a competing cone has to be defined at every
point of the cone's apex, and only a cover gives that.
`ComplexAnalytic.AnalyticSpace.Pullback.conePreimage_covers` is **the only declaration in this
file that turns `hU` into a cover**; `ComplexAnalytic.AnalyticSpace.Pullback.gluedLift`,
`…ofRestrict_comp_gluedLift`, `…gluedLift_p1` and `…gluedLift_p2` take `hU` and hand it to that
one, and nothing else in the file mentions it. **This section said until 2026-09-08 that *no
declaration below asks the `U i` to cover `X`*, and the lift retired it**; what survives of it is
the claim about the declarations through
`ComplexAnalytic.AnalyticSpace.Pullback.overlapLift_t_fV`, which is stated in this section's
opening paragraph.

**Joint surjectivity is still not enough to make `…glued` the fibre product**, and nothing below
claims that it is: `CategoryTheory.Limits.IsLimit` needs the *uniqueness* of the lift as well, and
that is not in this file. **It is in `Oka/AnalyticSpace/PullbackLimit.lean`**, which imports this
one and proves it there; the section headed *What this does not do* says what that took and what
it did not close.

## Main results

- `ComplexAnalytic.AnalyticSpace.Pullback.t'_fac` and
  `ComplexAnalytic.AnalyticSpace.Pullback.t'Map_fac`: the `t_fac` law, upstairs and downstairs.
- `ComplexAnalytic.AnalyticSpace.Pullback.gluing`: **the glue datum**, over
  `AlgebraicGeometry.LocallyRingedSpace`.
- `ComplexAnalytic.AnalyticSpace.Pullback.glueDataCLinear_gluing`: its transitions are
  `ℂ`-linear.
- `ComplexAnalytic.AnalyticSpace.Pullback.glued`: **the gluing, as a complex analytic space**, and
  `…glued_toLocallyRingedSpace`: its underlying locally ringed space is the datum's own gluing, so
  every statement of `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` about the gluing of a
  datum is a statement about it.
- `ComplexAnalytic.AnalyticSpace.Pullback.fV_comp_toBase` and `…fV_comp_snd`: the compatibility
  the two projections are glued from.
- `ComplexAnalytic.AnalyticSpace.Pullback.p1` and `…p2`: **the two projections, as morphisms of
  analytic spaces**, with `…ι_p1` and `…ι_p2` saying what each restricts to on a member.
- `ComplexAnalytic.AnalyticSpace.Pullback.toBase_comp`: the ambient pullback square's own
  commutation, which is `CategoryTheory.Limits.pullback.condition` at the cospan the family
  presents.
- `ComplexAnalytic.AnalyticSpace.Pullback.p_comm`: **the square commutes** — `p1 ≫ f = p2 ≫ g`.
- `ComplexAnalytic.AnalyticSpace.Pullback.ι`: **the `i`-th ambient pullback included in the
  gluing, as a morphism of analytic spaces**, with `…ι_comp_p1` and `…ι_comp_p2` reading the two
  projections along it. These are `…ι_p1` and `…ι_p2` with both sides analytic, which
  `ComplexAnalytic.AnalyticSpace.ιCLinear` is what makes possible.
- `ComplexAnalytic.AnalyticSpace.Pullback.fV_comp_ι`: **the glue condition with every morphism in
  it analytic.**
- `ComplexAnalytic.AnalyticSpace.Pullback.liftMember` and `…overlapLift`: **the pieces of a lift
  out of a competing cone, and their agreement over a double overlap** — `…liftMember_fst`,
  `…liftMember_snd`, `…overlapLift_fV`, `…overlapLift_snd` and `…overlapLift_t_fV`.
- `ComplexAnalytic.AnalyticSpace.Pullback.gluedLift`, `…gluedLift_p1` and `…gluedLift_p2`:
  **Mathlib's `AlgebraicGeometry.Scheme.Pullback.gluedLift` and its two factorisations, over
  `ComplexAnalytic.AnalyticSpace`** — a competing cone factors through the gluing. The
  *uniqueness* of the factorisation is not in this file; it is
  `ComplexAnalytic.AnalyticSpace.Pullback.gluedLift_uniq` in
  `Oka/AnalyticSpace/PullbackLimit.lean`.

## What this does not do

**It does not make `ComplexAnalytic.AnalyticSpace` a category with pullbacks, and nothing below
claims it does.** `CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` does not
synthesise at the commit that adds this file, and **it still does not at the commit that adds
`Oka/AnalyticSpace/PullbackLimit.lean`**, where the probe was re-run rather than carried over.
**It does synthesise at the commit that adds `Oka/AnalyticSpace/PullbackReduction.lean`**,
2026-09-08, where it was re-run again; the sentence recording the commit that adds this file and
the sentence recording the commit that adds `Oka/AnalyticSpace/PullbackLimit.lean` are pinned to
those commits and neither is retired by that. What is missing *here* is unchanged and is listed
below in Mathlib's order, with each item that has since been supplied elsewhere marked as such:

* **The uniqueness of the lift.** `ComplexAnalytic.AnalyticSpace.Pullback.gluedLift` and its two
  factorisations are below, so a competing cone *factors*; that the factorisation is unique is not
  in this file. **This bullet said until 2026-09-08 that the lift itself was absent and unpriced,
  and that is what the lift retired; on the same day it said of `pullbackP1Iso`, `pullbackFstιToV`
  and `lift_comp_ι` that none of the three is transcribed and none is priced, and
  `Oka/AnalyticSpace/PullbackLimit.lean` retired that too.** None of the three is transcribed
  there either, and the price is that none of them is needed: what an isomorphism onto `W ×_X U i`
  would be used for is to factor a morphism through
  `ComplexAnalytic.AnalyticSpace.Pullback.ι`, and a morphism whose image lies in the image of an
  open immersion factors through it without an object being named.
  `ComplexAnalytic.AnalyticSpace.Pullback.range_base_ι` is the image computation that replaces the
  isomorphism. `gluedLiftPullbackMap` was a different matter already: the route below does not use
  it and does not need it, because the pieces of the lift are open subspaces of the cone's apex
  rather than categorical pullbacks — **and the same reason turned out to dispose of the other
  three, which this bullet did not predict.**
* **`gluedIsLimit`**, which needs the uniqueness above and nothing else that is missing. It is
  `ComplexAnalytic.AnalyticSpace.Pullback.gluedIsLimit` in `Oka/AnalyticSpace/PullbackLimit.lean`,
  and it is built by `CategoryTheory.Limits.PullbackCone.isLimitAux'` rather than by
  `CategoryTheory.Limits.PullbackCone.IsLimit.mk`, which this bullet named; the five things it
  takes are the ones this bullet listed —
  `ComplexAnalytic.AnalyticSpace.Pullback.p_comm`, `…gluedLift`, `…gluedLift_p1`, `…gluedLift_p2`
  and the uniqueness.
* **`hasPullback_of_cover`** is `ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover`
  there, and **the reduction of an arbitrary cospan to one where the base change is known** is
  `Oka/AnalyticSpace/PullbackReduction.lean` — which covers `Y` and then `Z`, in that order, and
  ends at `ComplexAnalytic.AnalyticSpace.hasPullbacks`. **This bullet said until 2026-09-08 that
  the reduction *is not* supplied and that its length is still not measured anywhere in this
  repository, and that it was the one of the four items this file named which nothing had yet
  supplied.** All four are supplied now, and the length turned out to be six declarations for the
  reduction itself and two more for the local-model predicate it runs on.

`Oka/AnalyticSpace/FiniteEtaleOver.lean`'s bullet on base change is **not** falsified by this
file: base change of the class `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` across a general
square is a statement about a class and does not follow from a fibre product existing, and no
fibre product over a general cospan is produced below. **That reason outlived the fibre product
itself**: `Oka/AnalyticSpace/PullbackReduction.lean` produced one on 2026-09-08 and the bullet
there was narrowed rather than struck, on this same ground — which is the argument this sentence
was making, so it is unchanged apart from these words.
-/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace ComplexAnalytic.AnalyticSpace.Pullback

variable {X Y Z : AnalyticSpace.{u}} {I : Type u} (U : I → X.Opens) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [∀ i, HasPullback (X.ofRestrict (U i) ≫ f) g]

/-! ### The factorisation law the glue datum's `t_fac` field asks for -/

/-- **The `t_fac` law upstairs.**

Mathlib's proof of the `t_fac` field of `AlgebraicGeometry.Scheme.Pullback.gluing`, taken out of
the datum and stated on its own so that the transport downstairs has something to rewrite with.
The two `CategoryTheory.Limits.pullback.hom_ext`s and the six factorisation lemmas are Mathlib's
unchanged. -/
theorem t'_fac (i j k : I) :
    t' U f g i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t U f g i j := by
  apply pullback.hom_ext
  on_goal 1 => apply pullback.hom_ext
  all_goals
    simp only [t'_snd_fst_fst, t'_snd_fst_snd, t'_snd_snd, t_fst_fst, t_fst_snd, t_snd,
      Category.assoc]

/-- **The `t_fac` law downstairs**, which is the field
`AlgebraicGeometry.LocallyRingedSpace.GlueData` asks for.

`ComplexAnalytic.AnalyticSpace.Pullback.t'Map_snd` turns the left-hand side into a conjugating
isomorphism followed by the image of an analytic composite;
`ComplexAnalytic.AnalyticSpace.Pullback.t'_fac` rewrites that composite; and
`CategoryTheory.IsPullback.isoPullback_inv_fst` cancels the conjugation that is left against the
projection it was built from. **No square is reproved downstairs**, which is what the second half
of `Oka/AnalyticSpace/PullbackBlock.lean` exists to make true. -/
theorem t'Map_fac (i j k : I) :
    t'Map U f g i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ forgetToLocallyRingedSpace.map (t U f g i j) := by
  rw [t'Map_snd, t'_fac]
  simp only [Functor.map_comp, isoPullbackFV, IsPullback.isoPullback_inv_fst_assoc]

/-! ### The glue datum, and the analytic space it glues to -/

/-- **The glue datum of the fibre product**, over `AlgebraicGeometry.LocallyRingedSpace`.

Every field is the image under `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` of a
declaration of `Oka/AnalyticSpace/PullbackBlock.lean`, except `t'` and `cocycle`, which are
`ComplexAnalytic.AnalyticSpace.Pullback.t'Map` and `…t'Map_cocycle` on the nose, and `t_fac`,
which is `ComplexAnalytic.AnalyticSpace.Pullback.t'Map_fac`. The datum is stated one category down
because `ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` is, and because there is no glue datum
over `ComplexAnalytic.AnalyticSpace` in this repository. -/
noncomputable def gluing : LocallyRingedSpace.GlueData.{u} where
  J := I
  U i := forgetToLocallyRingedSpace.obj (pullback (X.ofRestrict (U i) ≫ f) g)
  V ij := forgetToLocallyRingedSpace.obj (v U f g ij.1 ij.2)
  f i j := forgetToLocallyRingedSpace.map (fV U f g i j)
  f_open i j := isOpenImmersion_map_fV U f g i j
  f_id i := by
    have : IsIso (fV U f g i i) := inferInstance
    infer_instance
  t i j := forgetToLocallyRingedSpace.map (t U f g i j)
  t_id i := by rw [t_id]; exact forgetToLocallyRingedSpace.map_id _
  t' i j k := t'Map U f g i j k
  t_fac i j k := t'Map_fac U f g i j k
  cocycle i j k := t'Map_cocycle U f g i j k

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- **The transitions of the datum are `ℂ`-linear.**

`ComplexAnalytic.glueDataCLinear_of_isCLinearHom` asks for linearity of the legs and of the
transitions, and both are field projections: the members carry the `ℂ`-algebra structures of the
analytic spaces they are the images of, and `ComplexAnalytic.AnalyticSpace.Hom` carries
`ComplexAnalytic.IsCLinearHom` in a field. So no analytic input is needed here, and that is the
use `Oka/AnalyticSpace/Glue.lean` states that lemma for. -/
theorem glueDataCLinear_gluing :
    ComplexAnalytic.GlueDataCLinear (gluing U f g)
      (fun j ↦ (pullback (X.ofRestrict (U j) ≫ f) g).algebraMap) :=
  glueDataCLinear_of_isCLinearHom _ _ (fun p ↦ (v U f g p.1 p.2).algebraMap)
    (fun i j ↦ (fV U f g i j).isCLinear) (fun i j ↦ (Pullback.t U f g i j).isCLinear)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- **The gluing, as a complex analytic space.**

`ComplexAnalytic.AnalyticSpace.ofGlueDataCLinear` at the datum, with the `HasLocalModels`
hypothesis discharged member by member from
`ComplexAnalytic.AnalyticSpace.hasLocalModels`. **This is not claimed to be the fibre product**:
the family of opens is not asked to cover `X`, and nothing below produces a limit cone. -/
noncomputable def glued : AnalyticSpace.{u} :=
  ofGlueDataCLinear (gluing U f g) _ (glueDataCLinear_gluing U f g)
    (fun j ↦ (pullback (X.ofRestrict (U j) ≫ f) g).hasLocalModels)

/-- **Its underlying locally ringed space is the one glued one category down**, so every statement
of `Oka/Geometry/RingedSpace/PresheafedSpace/Gluing.lean` about the datum is a statement about
this space. -/
@[simp]
theorem glued_toLocallyRingedSpace :
    (glued U f g).toLocallyRingedSpace = (gluing U f g).toGlueData.glued := rfl

/-! ### The two projections, and the square they make commute -/

/-- **The member maps agree over the overlaps, for the first projection.**

`ComplexAnalytic.AnalyticSpace.Pullback.t_fst_fst` read as a statement about the member maps of
the datum, which is the hypothesis
`ComplexAnalytic.AnalyticSpace.glueMorphismsOfGlueData` asks for. -/
theorem fV_comp_toBase (i j : I) :
    fV U f g i j ≫ toBase U f g i = t U f g i j ≫ fV U f g j i ≫ toBase U f g j := by
  simp [toBase, t_fst_fst_assoc, ← pullback.condition]

/-- **The member maps agree over the overlaps, for the second projection**, which is
`ComplexAnalytic.AnalyticSpace.Pullback.t_fst_snd` read the same way. -/
theorem fV_comp_snd (i j : I) :
    fV U f g i j ≫ pullback.snd (X.ofRestrict (U i) ≫ f) g =
      t U f g i j ≫ fV U f g j i ≫ pullback.snd (X.ofRestrict (U j) ≫ f) g := by
  simp [t_fst_snd]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- **The first projection**, `glued ⟶ X`, glued out of
`ComplexAnalytic.AnalyticSpace.Pullback.toBase`.

`ComplexAnalytic.AnalyticSpace.glueMorphismsOfGlueData` rather than
`CategoryTheory.Limits.Multicoequalizer.desc`, which is what Mathlib uses, because it returns a
morphism of **analytic spaces**. -/
noncomputable def p1 : glued U f g ⟶ X :=
  glueMorphismsOfGlueData (gluing U f g) _ (glueDataCLinear_gluing U f g)
    (fun j ↦ (pullback (X.ofRestrict (U j) ≫ f) g).hasLocalModels)
    (fun j ↦ forgetToLocallyRingedSpace.map (toBase U f g j))
    (fun i j ↦ by
      have h := congrArg forgetToLocallyRingedSpace.map (fV_comp_toBase U f g i j)
      simp only [Functor.map_comp] at h
      exact h)
    (fun j ↦ (toBase U f g j).isCLinear)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- **The second projection**, `glued ⟶ Y`, glued out of the second projections of the ambient
pullbacks. -/
noncomputable def p2 : glued U f g ⟶ Y :=
  glueMorphismsOfGlueData (gluing U f g) _ (glueDataCLinear_gluing U f g)
    (fun j ↦ (pullback (X.ofRestrict (U j) ≫ f) g).hasLocalModels)
    (fun j ↦ forgetToLocallyRingedSpace.map (pullback.snd (X.ofRestrict (U j) ≫ f) g))
    (fun i j ↦ by
      have h := congrArg forgetToLocallyRingedSpace.map (fV_comp_snd U f g i j)
      simp only [Functor.map_comp] at h
      exact h)
    (fun j ↦ (pullback.snd (X.ofRestrict (U j) ≫ f) g).isCLinear)

/-- **The ambient square commutes**, which is
`CategoryTheory.Limits.pullback.condition` at the cospan the `j`-th member presents, composed with
the open-subspace inclusion. -/
theorem toBase_comp (j : I) :
    toBase U f g j ≫ f = pullback.snd (X.ofRestrict (U j) ≫ f) g ≫ g := by
  simp [toBase, pullback.condition]

/-- **The first projection restricts to `…toBase` on the `j`-th member.**

The statement is about the underlying morphism of locally ringed spaces because that is where
`ComplexAnalytic.AnalyticSpace.ι_glueMorphismsOfGlueData`, which proves it, is stated.

**The reason given here until 2026-09-08 was that the members of a glue datum *are not objects of
`ComplexAnalytic.AnalyticSpace`*, and that is now too strong** — a member together with the
structure and charts this datum's caller supplied is one, and
`ComplexAnalytic.AnalyticSpace.Pullback.ι_comp_p1` below is this statement with both sides
analytic. This one is kept because it is what
`ComplexAnalytic.AnalyticSpace.ι_glueMorphismsOfGlueData` gives directly and what
`ComplexAnalytic.AnalyticSpace.Pullback.p_comm` consumes. -/
theorem ι_p1 (j : I) :
    (gluing U f g).toGlueData.ι j ≫ (p1 U f g).toLRSHom =
      forgetToLocallyRingedSpace.map (toBase U f g j) :=
  ι_glueMorphismsOfGlueData (gluing U f g) _ (glueDataCLinear_gluing U f g) _
    (fun j ↦ forgetToLocallyRingedSpace.map (toBase U f g j)) _ _ j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- **The second projection restricts to the ambient second projection on the `j`-th member.** -/
theorem ι_p2 (j : I) :
    (gluing U f g).toGlueData.ι j ≫ (p2 U f g).toLRSHom =
      forgetToLocallyRingedSpace.map (pullback.snd (X.ofRestrict (U j) ≫ f) g) :=
  ι_glueMorphismsOfGlueData (gluing U f g) _ (glueDataCLinear_gluing U f g) _
    (fun j ↦ forgetToLocallyRingedSpace.map (pullback.snd (X.ofRestrict (U j) ≫ f) g)) _ _ j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- **The square commutes.**

Checked member by member: `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` is faithful,
`AlgebraicGeometry.LocallyRingedSpace.GlueData.hom_ext` reduces an equation on the gluing to one
on each member, and there the two sides are the images of the two sides of
`ComplexAnalytic.AnalyticSpace.Pullback.toBase_comp`. **This is a statement about morphisms of
analytic spaces**; the reduction to locally ringed spaces is the proof and not the statement. -/
theorem p_comm : p1 U f g ≫ f = p2 U f g ≫ g := by
  apply forgetToLocallyRingedSpace.map_injective
  refine (gluing U f g).hom_ext _ _ fun j ↦ ?_
  change (gluing U f g).toGlueData.ι j ≫ (p1 U f g).toLRSHom ≫ _ =
    (gluing U f g).toGlueData.ι j ≫ (p2 U f g).toLRSHom ≫ _
  rw [← Category.assoc, ← Category.assoc, ι_p1, ι_p2]
  have h := congrArg forgetToLocallyRingedSpace.map (toBase_comp U f g j)
  simp only [Functor.map_comp] at h
  exact h

/-! ### The members of the gluing, as analytic morphisms -/

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- **The `i`-th ambient pullback includes into the gluing, as a morphism of analytic spaces.**

`ComplexAnalytic.AnalyticSpace.ιCLinear` at this datum. The member of the datum at `i` is
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace.obj` of the ambient pullback and the
structure it is given is that pullback's own, so the object `…ιCLinear` returns is the pullback
itself and the statement below needs no transport.

**This is what `…ι_p1` and `…ι_p2` could not say.** Those are equations one category down because
the composite in them has `ι j` in it and `ι j` was only a morphism of locally ringed spaces;
with this it is a morphism of analytic spaces and
`ComplexAnalytic.AnalyticSpace.Pullback.ι_comp_p1` says the same thing upstairs. -/
noncomputable def ι (i : I) : pullback (X.ofRestrict (U i) ≫ f) g ⟶ glued U f g :=
  ιCLinear (gluing U f g) _ (glueDataCLinear_gluing U f g)
    (fun j ↦ (pullback (X.ofRestrict (U j) ≫ f) g).hasLocalModels) i

/-- Its underlying morphism of locally ringed spaces is the datum's own inclusion, by `rfl`. -/
@[simp]
theorem toLRSHom_ι (i : I) : (ι U f g i).toLRSHom = (gluing U f g).toGlueData.ι i := rfl

/-- **The glue condition, upstairs**: the two ways of including the overlap `V i j` into the
gluing agree.

`CategoryTheory.GlueData.glue_condition` at this datum, reflected along the
faithful `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`. Every morphism named here is
analytic, which is the whole point of stating it: it is the hypothesis
`ComplexAnalytic.AnalyticSpace.glueMorphismsOfOpens` needs when the pieces of a lift are composed
with `ComplexAnalytic.AnalyticSpace.Pullback.ι`. -/
theorem fV_comp_ι (i j : I) :
    fV U f g i j ≫ ι U f g i = t U f g i j ≫ fV U f g j i ≫ ι U f g j := by
  apply forgetToLocallyRingedSpace.map_injective
  simp only [Functor.map_comp]
  exact ((gluing U f g).toGlueData.glue_condition i j).symm

/-- **`ComplexAnalytic.AnalyticSpace.Pullback.ι_p1` with both sides analytic.** -/
@[simp]
theorem ι_comp_p1 (i : I) : ι U f g i ≫ p1 U f g = toBase U f g i := by
  apply forgetToLocallyRingedSpace.map_injective
  simp only [Functor.map_comp]
  exact ι_p1 U f g i

/-- **`ComplexAnalytic.AnalyticSpace.Pullback.ι_p2` with both sides analytic.** -/
@[simp]
theorem ι_comp_p2 (i : I) :
    ι U f g i ≫ p2 U f g = pullback.snd (X.ofRestrict (U i) ≫ f) g := by
  apply forgetToLocallyRingedSpace.map_injective
  simp only [Functor.map_comp]
  exact ι_p2 U f g i

/-! ### The lift of a competing cone -/

variable (s : PullbackCone f g)

/-- **The preimage of `U i` under the cone's first leg**, which is the family of opens the lift is
glued over. -/
noncomputable abbrev conePreimage (i : I) : (s.pt : AnalyticSpace.{u}).Opens :=
  (TopologicalSpace.Opens.map (s.fst : s.pt ⟶ X).toLRSHom.base).obj (U i)

/-- **The `i`-th piece of the lift**, `s.pt|(s.fst ⁻¹' U i) ⟶ U i ×_Z Y`.

The two legs are `ComplexAnalytic.AnalyticSpace.restrictHom` — the cone's own first leg restricted
to the preimage, which is where the *shape* of this construction differs from Mathlib's — and the
cone's second leg. The square commutes by
`ComplexAnalytic.AnalyticSpace.restrictHom_fac` and the cone's own condition.

**Mathlib reaches the same morphism through `gluedLiftPullbackMap`, a
`pullbackRightPullbackFstIso` and a `pullbackSymmetry`.** It has to, because there the pieces of
the source are the members of `𝒰.pullback₁ s.fst`, which are categorical pullbacks; here they are
open subspaces of `s.pt` and `…restrictHom` is the map into `U i` on the nose. Nothing in this
file transcribes `gluedLiftPullbackMap` and nothing needs it. -/
noncomputable def liftMember (i : I) :
    s.pt.restrict (conePreimage U f g s i) ⟶ pullback (X.ofRestrict (U i) ≫ f) g :=
  pullback.lift (restrictHom s.fst (U i))
    (s.pt.ofRestrict (conePreimage U f g s i) ≫ s.snd)
    (by rw [← Category.assoc, restrictHom_fac, Category.assoc, Category.assoc, s.condition])

/-- Its first component. -/
@[simp]
theorem liftMember_fst (i : I) :
    liftMember U f g s i ≫ pullback.fst (X.ofRestrict (U i) ≫ f) g = restrictHom s.fst (U i) :=
  pullback.lift_fst _ _ _

/-- Its second component. -/
@[simp]
theorem liftMember_snd (i : I) :
    liftMember U f g s i ≫ pullback.snd (X.ofRestrict (U i) ≫ f) g =
      s.pt.ofRestrict (conePreimage U f g s i) ≫ s.snd :=
  pullback.lift_snd _ _ _

/-- **The double overlap of the lift's pieces, mapped into the block's overlap object.**

`ComplexAnalytic.AnalyticSpace.Pullback.v` at `i j` is `(U i ×_Z Y) ×_X U j`, so a morphism into
it is a pair: the `i`-th piece of the lift restricted to the overlap, and the cone's first leg
restricted into `U j`. The square commutes because both composites are the inclusion of the
double overlap into `s.pt` followed by `s.fst`. -/
noncomputable def overlapLift (i j : I) :
    s.pt.restrict (conePreimage U f g s i ⊓ conePreimage U f g s j) ⟶ v U f g i j :=
  pullback.lift
    (s.pt.restrictLE (inf_le_left : conePreimage U f g s i ⊓ conePreimage U f g s j ≤ _) ≫
      liftMember U f g s i)
    (s.pt.restrictLE (inf_le_right : conePreimage U f g s i ⊓ conePreimage U f g s j ≤ _) ≫
      restrictHom s.fst (U j))
    (by
      rw [Category.assoc, Category.assoc, ← Category.assoc (liftMember U f g s i),
        liftMember_fst, restrictHom_fac, restrictHom_fac, ← Category.assoc, ← Category.assoc,
        restrictLE_fac, restrictLE_fac])

/-- **Composed with the member map of the datum it is the `i`-th piece**, by construction. -/
@[reassoc]
theorem overlapLift_fV (i j : I) :
    overlapLift U f g s i j ≫ fV U f g i j =
      s.pt.restrictLE (inf_le_left : conePreimage U f g s i ⊓ conePreimage U f g s j ≤ _) ≫
        liftMember U f g s i :=
  pullback.lift_fst _ _ _

/-- **Its second component**, by construction. -/
theorem overlapLift_snd (i j : I) :
    overlapLift U f g s i j ≫ pullback.snd _ _ =
      s.pt.restrictLE (inf_le_right : conePreimage U f g s i ⊓ conePreimage U f g s j ≤ _) ≫
        restrictHom s.fst (U j) :=
  pullback.lift_snd _ _ _

/-- **Composed with the *other* member map, across the transition, it is the `j`-th piece.**

This is the one statement about `ComplexAnalytic.AnalyticSpace.Pullback.overlapLift` that is not
one of its two components, and it is where
`ComplexAnalytic.AnalyticSpace.Pullback.t_fst_fst` and `…t_fst_snd` are used:
the first says the transition sends the `i`-side's `U j`-component to the `j`-side's
`U j`-component, the second that it leaves the `Y`-component alone. Both components then reduce
to the inclusion of the double overlap, by
`ComplexAnalytic.AnalyticSpace.restrictLE_fac` on each side. -/
@[reassoc]
theorem overlapLift_t_fV (i j : I) :
    overlapLift U f g s i j ≫ t U f g i j ≫ fV U f g j i =
      s.pt.restrictLE (inf_le_right : conePreimage U f g s i ⊓ conePreimage U f g s j ≤ _) ≫
        liftMember U f g s j := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, t_fst_fst, overlapLift_snd, Category.assoc,
      liftMember_fst]
  · rw [Category.assoc, Category.assoc, t_fst_snd, overlapLift_fV_assoc, Category.assoc,
      liftMember_snd, liftMember_snd, ← Category.assoc, ← Category.assoc, restrictLE_fac,
      restrictLE_fac]

variable (hU : ∀ x : X, ∃ i, x ∈ U i)

omit [∀ i, HasPullback (X.ofRestrict (U i) ≫ f) g] in
include hU in
/-- **The preimages of a covering family cover.** The only place the hypothesis that the `U i`
cover `X` is turned into a cover; the module docstring's section
*Where the covering hypothesis enters, and it is one declaration deep* says which declarations
take it and where it goes. -/
theorem conePreimage_covers : ∀ p : s.pt, ∃ i, p ∈ conePreimage U f g s i :=
  fun p ↦ (hU ((s.fst : s.pt ⟶ X).toLRSHom.base p)).imp fun _ h ↦ h

/-- **The pieces of the lift agree on the double overlaps**, which is the hypothesis
`ComplexAnalytic.AnalyticSpace.glueMorphismsOfOpens` asks for.

Both sides factor through `ComplexAnalytic.AnalyticSpace.Pullback.overlapLift`, by
`…overlapLift_fV` and `…overlapLift_t_fV`, and there the two are the two sides of
`ComplexAnalytic.AnalyticSpace.Pullback.fV_comp_ι` — the glue condition of the datum. **No
computation with `t'` is involved**: the cocycle law is the datum's business and was discharged
when it was built. -/
theorem restrictLE_comp_liftMember_comp_ι (i j : I) :
    s.pt.restrictLE (inf_le_left : conePreimage U f g s i ⊓ conePreimage U f g s j ≤ _) ≫
        (liftMember U f g s i ≫ ι U f g i) =
      s.pt.restrictLE (inf_le_right : conePreimage U f g s i ⊓ conePreimage U f g s j ≤ _) ≫
        (liftMember U f g s j ≫ ι U f g j) := by
  rw [← overlapLift_fV_assoc, fV_comp_ι, overlapLift_t_fV_assoc]

/-- **The lift of a competing cone into the gluing** — Mathlib's
`AlgebraicGeometry.Scheme.Pullback.gluedLift`, over `ComplexAnalytic.AnalyticSpace`.

`ComplexAnalytic.AnalyticSpace.glueMorphismsOfOpens` at the preimage family, whose pieces are
`ComplexAnalytic.AnalyticSpace.Pullback.liftMember` followed by
`ComplexAnalytic.AnalyticSpace.Pullback.ι` and whose compatibility is
`ComplexAnalytic.AnalyticSpace.Pullback.restrictLE_comp_liftMember_comp_ι`.

**This is where the `U i` are first asked to cover `X`.** Everything before it in this file and in
`Oka/AnalyticSpace/PullbackBlock.lean` is about an arbitrary family of opens; a lift out of `s.pt`
has to be defined at every point of `s.pt`, and only a cover gives that. -/
noncomputable def gluedLift : s.pt ⟶ glued U f g :=
  glueMorphismsOfOpens (conePreimage U f g s) (conePreimage_covers U f g s hU)
    (fun i ↦ liftMember U f g s i ≫ ι U f g i)
    (restrictLE_comp_liftMember_comp_ι U f g s)

/-- **The lift restricts to its `i`-th piece**, which is what the two factorisations below
consume. -/
@[simp]
theorem ofRestrict_comp_gluedLift (i : I) :
    s.pt.ofRestrict (conePreimage U f g s i) ≫ gluedLift U f g s hU =
      liftMember U f g s i ≫ ι U f g i :=
  ofRestrict_comp_glueMorphismsOfOpens _ _ _ _ i

/-- **The lift factors the cone's first leg** — Mathlib's
`AlgebraicGeometry.Scheme.Pullback.gluedLift_p1`.

Checked on each member of the preimage family by
`ComplexAnalytic.AnalyticSpace.hom_ext_of_opens`: there the lift is its `i`-th piece, `p1` reads
it by `ComplexAnalytic.AnalyticSpace.Pullback.ι_comp_p1`, and what is left is
`ComplexAnalytic.AnalyticSpace.restrictHom_fac`. -/
theorem gluedLift_p1 : gluedLift U f g s hU ≫ p1 U f g = s.fst := by
  refine hom_ext_of_opens (conePreimage U f g s) (conePreimage_covers U f g s hU) fun i ↦ ?_
  have h : liftMember U f g s i ≫ pullback.fst (X.ofRestrict (U i) ≫ f) g ≫
      X.ofRestrict (U i) = s.pt.ofRestrict (conePreimage U f g s i) ≫ s.fst := by
    rw [← Category.assoc, liftMember_fst, restrictHom_fac]
  rw [← Category.assoc, ofRestrict_comp_gluedLift, Category.assoc, ι_comp_p1]
  exact h

/-- **The lift factors the cone's second leg** — Mathlib's
`AlgebraicGeometry.Scheme.Pullback.gluedLift_p2`. The same check, ending in
`ComplexAnalytic.AnalyticSpace.Pullback.liftMember_snd` rather than in a restriction square. -/
theorem gluedLift_p2 : gluedLift U f g s hU ≫ p2 U f g = s.snd := by
  refine hom_ext_of_opens (conePreimage U f g s) (conePreimage_covers U f g s hU) fun i ↦ ?_
  rw [← Category.assoc, ofRestrict_comp_gluedLift, Category.assoc, ι_comp_p2, liftMember_snd]

end ComplexAnalytic.AnalyticSpace.Pullback
