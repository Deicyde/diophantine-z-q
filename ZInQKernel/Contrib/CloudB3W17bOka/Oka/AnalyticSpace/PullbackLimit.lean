/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.PullbackGlue

/-!
# The gluing **is** the fibre product: uniqueness of the lift, the limit cone, and `HasPullback`

`Oka/AnalyticSpace/PullbackGlue.lean` glues the ambient pullbacks `Uᵢ ×_Z Y` into an analytic
space `ComplexAnalytic.AnalyticSpace.Pullback.glued`, produces the two projections
`…p1` and `…p2` and the square `…p_comm` they make commute, and lifts a competing cone into it
with `…gluedLift`, `…gluedLift_p1` and `…gluedLift_p2`. Its own *What this does not do* names
what is left, and the first item is the **uniqueness** of that lift.

**This file is that item and the two that follow from it.** It proves the lift unique, assembles
the limit cone `ComplexAnalytic.AnalyticSpace.Pullback.gluedIsLimit`, and concludes
`ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover`: a cospan whose first leg has a base
covered by opens along which the base change already exists has a fibre product.

## The one geometric fact, and it is the whole of the work

Uniqueness reduces, by `ComplexAnalytic.AnalyticSpace.hom_ext_of_opens` over the preimage family
`ComplexAnalytic.AnalyticSpace.Pullback.conePreimage`, to a statement about one member: the
restriction of a competing `m` to `s.fst ⁻¹' Uᵢ` agrees with the `i`-th piece of the lift. Both
sides land in the image of `ComplexAnalytic.AnalyticSpace.Pullback.ι`, and once they are read
there the comparison is `CategoryTheory.Limits.pullback.hom_ext` on the ambient pullback and
nothing else.

**Reading them there is the fact that had to be proved**, and it is
`ComplexAnalytic.AnalyticSpace.Pullback.range_base_ι`:

    Set.range (ι i).base = p1 ⁻¹' Uᵢ

The inclusion `⊆` is `…ι_comp_p1` — the composite is
`ComplexAnalytic.AnalyticSpace.Pullback.toBase`, which factors through `Uᵢ`. **The inclusion `⊇`
is where the glue datum is used**, and it is the only point in this file where a point of the
gluing is decomposed:

* `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_jointly_surjective` writes the point as
  `ι j q`, for some `j` and some `q` of the `j`-th ambient pullback;
* `…ι_comp_p1` turns the hypothesis into `toBase j q ∈ Uᵢ`, so `q` lies in the preimage of `Uᵢ`
  under `toBase j`;
* that preimage **is** the image of `ComplexAnalytic.AnalyticSpace.Pullback.fV j i`, by
  `ComplexAnalytic.AnalyticSpace.range_base_pullbackFst_ofRestrict` — the member map of the datum
  is a base change of the inclusion of `Uᵢ` and its image is what one expects of one;
* and `ComplexAnalytic.AnalyticSpace.Pullback.fV_comp_ι`, the glue condition, moves the resulting
  point across the transition into the image of `ι i`.

**No `t'` and no cocycle appears**, which is the same division of labour the lift's own
compatibility lemma reports: the cocycle law was discharged when the datum was built.

## This is `pullbackP1Iso`'s content, and not its statement

Mathlib gets uniqueness from `AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso`, an isomorphism
`W ×_X Uᵢ ≅ Uᵢ ×_Z Y`, and that isomorphism needs
`AlgebraicGeometry.Scheme.Pullback.lift_comp_ι` before it, which needs
`AlgebraicGeometry.Scheme.Pullback.pullbackFstιToV` before *it*. **None of those three is
transcribed here and none is needed**, and neither is
`AlgebraicGeometry.Scheme.Pullback.gluedLiftPullbackMap`, which is not one of the three — it
belongs to Mathlib's route to the lift rather than to its route to uniqueness, and
`Oka/AnalyticSpace/PullbackGlue.lean` had already disposed of it there.

**The reason that file gave for `gluedLiftPullbackMap` is the reason for the other three as
well**, which is what it did not predict: the pieces of the lift are open subspaces of the cone's
apex rather than categorical pullbacks, so what an isomorphism onto `W ×_X Uᵢ` would be used for
is to *factor a morphism through `ι i`* — and a morphism whose image lies in the image of an open
immersion factors through it directly, with no object named.

That factorisation is `ComplexAnalytic.AnalyticSpace.Pullback.liftι`, which is
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift` at `(ι i).toLRSHom` with its
`ℂ`-linearity supplied by `ComplexAnalytic.IsCLinearHom.of_comp` at the factorisation — the same
two-line promotion `ComplexAnalytic.AnalyticSpace.liftRestrict` is built by. The open-immersion
hypothesis it needs is `ComplexAnalytic.AnalyticSpace.Pullback.isOpenImmersion_toLRSHom_ι`, which
is `AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_isOpenImmersion` after
`ComplexAnalytic.AnalyticSpace.Pullback.toLRSHom_ι` has rewritten the goal to the datum's own
inclusion. **It is a theorem and not an instance**, for the reason
`ComplexAnalytic.AnalyticSpace.isOpenImmersion_map_pullbackFst_ofRestrict` gives for the same
shape: the two spellings are `rfl`-equal and are different discrimination-tree keys, so a caller
ascribes it in a `haveI` rather than a key being added to the instance graph.

## Main results

- `ComplexAnalytic.AnalyticSpace.Pullback.range_base_ι`: **the image of the `i`-th member of the
  gluing is the preimage of `Uᵢ` under the first projection.**
- `ComplexAnalytic.AnalyticSpace.Pullback.isOpenImmersion_toLRSHom_ι`: the underlying morphism of
  that member inclusion is an open immersion of locally ringed spaces.
- `ComplexAnalytic.AnalyticSpace.Pullback.liftι` and
  `ComplexAnalytic.AnalyticSpace.Pullback.liftι_fac`: **a morphism into the gluing whose image
  lies in that member factors through it**, as a morphism of analytic spaces.
- `ComplexAnalytic.AnalyticSpace.Pullback.range_base_ofRestrict_comp_subset_ι`: a
  competing cone's `m`, restricted to `s.fst ⁻¹' Uᵢ`, satisfies that hypothesis.
- `ComplexAnalytic.AnalyticSpace.Pullback.liftι_eq_liftMember`: **the factorisation it produces is
  the `i`-th piece of the lift**, by `CategoryTheory.Limits.pullback.hom_ext`.
- `ComplexAnalytic.AnalyticSpace.Pullback.gluedLift_uniq`: **the lift is unique** — Mathlib's
  `AlgebraicGeometry.Scheme.Pullback.gluedIsLimit`'s uniqueness half, over
  `ComplexAnalytic.AnalyticSpace`.
- `ComplexAnalytic.AnalyticSpace.Pullback.gluedIsLimit`: **the gluing is the fibre product** —
  the limit cone.
- `ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover`: **the cospan has a fibre
  product**, Mathlib's `AlgebraicGeometry.Scheme.Pullback.hasPullback_of_cover`.

## What this does not do

* **It does not make `ComplexAnalytic.AnalyticSpace` a category with pullbacks, and nothing below
  does.** `ComplexAnalytic.AnalyticSpace.Pullback.hasPullback_of_cover` asks for a family of opens
  of `X` which covers `X` **and along which the base change is already known** — the hypothesis
  `[∀ i, HasPullback (X.ofRestrict (U i) ≫ f) g]`, inherited from
  `Oka/AnalyticSpace/PullbackBlock.lean` — and nothing here produces such a family for a general
  `f` and `g`. `#synth CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` fails at
  the commit that adds this file, run with the category positional and not grepped.

  **The bullet ended there, and said in its own words that the probe fails, until 2026-09-08**,
  when `Oka/AnalyticSpace/PullbackReduction.lean` produced that family and
  `ComplexAnalytic.AnalyticSpace.hasPullbacks` made the probe succeed. The `#synth` sentence above
  is pinned to the commit that adds *this* file and is unaffected; what is retired is the reading
  of it as a claim about the tree, and the words *nothing below does* are what replace that
  reading, `below` being this file.
* **It does not do the reduction of a general cospan**, which is what would produce that family:
  Mathlib covers `X` by affines, then `Y`, then `Z`, and takes three theorems and two symmetry
  arguments to do it. The analytic analogue covers by local models and is
  `Oka/AnalyticSpace/PullbackReduction.lean`: six declarations for the reduction, of which four are
  the transcribable ones — the base case, the two covers and the family a general cospan needs —
  and two more for the predicate *is a local model on the nose* that the substitutions run on.

  **This bullet read *The analytic analogue would cover by local models, and its length is not
  measured anywhere in this repository* until 2026-09-08**, and *The three declarations named as
  still owed by `Oka/AnalyticSpace/PullbackGlue.lean`'s* What this does not do *are the ones below;
  the fourth item, the reduction, is untouched by this file and stays owed.* Both were exact when
  written; taxis #1909 measured the length and the file above supplied it, and the fourth item is
  no longer owed by anything.
* **It states no `CategoryTheory.IsPullback`.** `…gluedIsLimit` is a
  `CategoryTheory.Limits.IsLimit` of the cone `…p_comm` presents, which is what
  `CategoryTheory.Limits.HasPullback` consumes; the `CategoryTheory.IsPullback` spelling would be
  one `CategoryTheory.IsPullback.of_isLimit` away and nothing in this repository asks for it yet.
* **Nothing about base change of a class along the projections.**
  `Oka/AnalyticSpace/FiniteEtaleOver.lean`'s bullet on base change is a statement about
  `ComplexAnalytic.AnalyticSpace.IsFiniteEtale` and does not follow from a fibre product existing;
  the same sentence appears at the foot of `Oka/AnalyticSpace/PullbackGlue.lean` and this file
  does not change it.
-/

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace ComplexAnalytic.AnalyticSpace.Pullback

variable {X Y Z : AnalyticSpace.{u}} {I : Type u} (U : I → X.Opens) (f : X ⟶ Z) (g : Y ⟶ Z)
variable [∀ i, HasPullback (X.ofRestrict (U i) ≫ f) g]

/-! ### The image of a member of the gluing -/

/-- **The image of the `i`-th member of the gluing is the preimage of `Uᵢ` under the first
projection.**

This is the one geometric fact this file proves and everything else in it is bookkeeping; the
module docstring's section *The one geometric fact, and it is the whole of the work* gives the
four steps of `⊇` and says which declaration supplies each.

**`⊆` costs nothing**: `ComplexAnalytic.AnalyticSpace.Pullback.ι_comp_p1` reads the composite as
`ComplexAnalytic.AnalyticSpace.Pullback.toBase`, whose second factor is the inclusion of `Uᵢ`, so
every point of the image is in `Uᵢ` by the second component of a point of an open subspace.

**`⊇` is where the datum is used**, and the step that is not formal is the third: the preimage of
`Uᵢ` under `toBase j` is the *image* of the member map `fV j i`, which holds because that member
map is a base change of the inclusion of `Uᵢ` and
`ComplexAnalytic.AnalyticSpace.range_base_pullbackFst_ofRestrict` computes the image of such a
base change. **No `t'` and no cocycle law appears here**; the transition `t j i` is used only to
move the point, by the glue condition
`ComplexAnalytic.AnalyticSpace.Pullback.fV_comp_ι`. -/
theorem range_base_ι (i : I) :
    Set.range ((ι U f g i).toLRSHom.base) =
      ((p1 U f g).toLRSHom.base : glued U f g → X) ⁻¹' (U i : Set X) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨q, rfl⟩
    have hc : (((ι U f g i ≫ p1 U f g)).toLRSHom.base : _ → X) q =
        ((p1 U f g).toLRSHom.base : glued U f g → X)
          (((ι U f g i).toLRSHom.base : _ → glued U f g) q) := rfl
    rw [Set.mem_preimage, ← hc, ι_comp_p1]
    exact (((pullback.fst (X.ofRestrict (U i) ≫ f) g).toLRSHom.base :
      _ → X.restrict (U i)) q).2
  · intro p hp
    obtain ⟨j, q, hq⟩ := LocallyRingedSpace.GlueData.ι_jointly_surjective (gluing U f g) p
    rw [← toLRSHom_ι U f g j] at hq
    have hq' : ((ι U f g j).toLRSHom.base : _ → glued U f g) q = p := hq
    have hmem : ((toBase U f g j).toLRSHom.base : _ → X) q ∈ (U i : Set X) := by
      have hc : (((ι U f g j ≫ p1 U f g)).toLRSHom.base : _ → X) q =
          ((p1 U f g).toLRSHom.base : glued U f g → X)
            (((ι U f g j).toLRSHom.base : _ → glued U f g) q) := rfl
      rw [← ι_comp_p1 U f g j, hc, hq']
      exact hp
    obtain ⟨r, hr⟩ : q ∈ Set.range ((fV U f g j i).toLRSHom.base) := by
      rw [range_base_pullbackFst_ofRestrict (toBase U f g j) (U i)]
      exact hmem
    refine ⟨(fV U f g i j).toLRSHom.base ((t U f g j i).toLRSHom.base r), ?_⟩
    have h := congrArg (fun (ψ : v U f g j i ⟶ glued U f g) ↦ (ψ.toLRSHom.base : _ → _) r)
      (fV_comp_ι U f g j i)
    rw [← hq', ← hr]
    exact h.symm

/-- **The `i`-th member inclusion is an open immersion of locally ringed spaces.**

`AlgebraicGeometry.LocallyRingedSpace.GlueData.ι_isOpenImmersion` at the datum, after
`ComplexAnalytic.AnalyticSpace.Pullback.toLRSHom_ι` has rewritten the goal into the datum's own
inclusion.

**A theorem and not an instance**, for the reason
`ComplexAnalytic.AnalyticSpace.isOpenImmersion_map_pullbackFst_ofRestrict` gives for the same
shape and which `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict` states in
general: the analytic spelling and the locally-ringed-space one are `rfl`-equal and are different
discrimination-tree keys, so instance search does not cross between them and the remedy this
repository has settled on is a `haveI` at the point of use rather than a new key. -/
theorem isOpenImmersion_toLRSHom_ι (i : I) :
    LocallyRingedSpace.IsOpenImmersion (ι U f g i).toLRSHom := by
  rw [toLRSHom_ι]
  exact LocallyRingedSpace.GlueData.ι_isOpenImmersion (gluing U f g) i

/-! ### Factoring through a member -/

/-- **A morphism into the gluing whose image lies in the `i`-th member factors through it**, as a
morphism of complex analytic spaces.

`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift` one category down, promoted by
`ComplexAnalytic.IsCLinearHom.of_comp` at its own factorisation — the same two-line construction
`ComplexAnalytic.AnalyticSpace.liftRestrict` is, and for the same reason: the lift is a morphism
*over* the gluing, both the morphism it factors and the member inclusion are `ℂ`-linear, so
linearity of the factor is contravariant functoriality of `Γ` and nothing is transported.

**This is what stands in for Mathlib's `AlgebraicGeometry.Scheme.Pullback.pullbackP1Iso`.** That
isomorphism exists there to say which object the preimage of `Uᵢ` in the gluing is; here the
question a caller asks is only *does this morphism factor through `ι i`*, and an open immersion
answers that from a containment of images without an object being named. -/
noncomputable def liftι {T : AnalyticSpace.{u}} (i : I) (h : T ⟶ glued U f g)
    (hr : Set.range (h.toLRSHom.base : T → glued U f g) ⊆
      Set.range ((ι U f g i).toLRSHom.base)) :
    T ⟶ pullback (X.ofRestrict (U i) ≫ f) g :=
  haveI := isOpenImmersion_toLRSHom_ι U f g i
  ⟨LocallyRingedSpace.IsOpenImmersion.lift (ι U f g i).toLRSHom h.toLRSHom hr,
    IsCLinearHom.of_comp
      (LocallyRingedSpace.IsOpenImmersion.lift_fac (ι U f g i).toLRSHom h.toLRSHom hr)
      h.isCLinear (ι U f g i).isCLinear⟩

/-- **It is a factorisation**, which is what every use of it consumes: the lift itself is opaque
and the composite is not. -/
theorem liftι_fac {T : AnalyticSpace.{u}} (i : I) (h : T ⟶ glued U f g)
    (hr : Set.range (h.toLRSHom.base : T → glued U f g) ⊆
      Set.range ((ι U f g i).toLRSHom.base)) :
    liftι U f g i h hr ≫ ι U f g i = h := by
  haveI := isOpenImmersion_toLRSHom_ι U f g i
  exact forgetToLocallyRingedSpace.map_injective
    (LocallyRingedSpace.IsOpenImmersion.lift_fac (ι U f g i).toLRSHom h.toLRSHom hr)

/-! ### The uniqueness of the lift -/

variable (s : PullbackCone f g)

/-- **A competing cone's morphism, restricted to `s.fst ⁻¹' Uᵢ`, lands in the `i`-th member.**

This is the hypothesis `ComplexAnalytic.AnalyticSpace.Pullback.liftι` asks for, discharged from
the *first* of the two triangles alone: `ComplexAnalytic.AnalyticSpace.Pullback.range_base_ι`
turns the goal into a statement about `p1`, `h₁` turns `p1 ∘ m` into `s.fst`, and what is left is
that a point of `s.pt|(s.fst ⁻¹' Uᵢ)` is in `s.fst ⁻¹' Uᵢ` by its own second component. **The
second triangle is not used here** and is not needed until the two components are compared. -/
theorem range_base_ofRestrict_comp_subset_ι (m : s.pt ⟶ glued U f g)
    (h₁ : m ≫ p1 U f g = s.fst) (i : I) :
    Set.range (((s.pt.ofRestrict (conePreimage U f g s i)) ≫ m).toLRSHom.base) ⊆
      Set.range ((ι U f g i).toLRSHom.base) := by
  rw [range_base_ι]
  rintro _ ⟨w, rfl⟩
  have hc : (((s.pt.ofRestrict (conePreimage U f g s i)) ≫ m).toLRSHom.base : _ → glued U f g) w =
      (m.toLRSHom.base : s.pt → glued U f g)
        (((s.pt.ofRestrict (conePreimage U f g s i)).toLRSHom.base : _ → s.pt) w) := rfl
  have hc' : ((m ≫ p1 U f g).toLRSHom.base : s.pt → X)
        (((s.pt.ofRestrict (conePreimage U f g s i)).toLRSHom.base : _ → s.pt) w) =
      ((p1 U f g).toLRSHom.base : glued U f g → X)
        ((m.toLRSHom.base : s.pt → glued U f g)
          (((s.pt.ofRestrict (conePreimage U f g s i)).toLRSHom.base : _ → s.pt) w)) := rfl
  rw [Set.mem_preimage, hc, ← hc', h₁]
  exact w.2

/-- **That factorisation is the `i`-th piece of the lift.**

`CategoryTheory.Limits.pullback.hom_ext` on the ambient pullback, one component from each
triangle of the cone:

* the first component is read through
  `ComplexAnalytic.AnalyticSpace.Pullback.toBase`, where `h₁` gives
  `ofRestrict (s.fst ⁻¹' Uᵢ) ≫ s.fst` and `ComplexAnalytic.AnalyticSpace.restrictHom_fac` gives
  the same of `ComplexAnalytic.AnalyticSpace.restrictHom`; the inclusion of `Uᵢ` is then cancelled
  as a monomorphism, which is `ComplexAnalytic.AnalyticSpace.mono_ofRestrict`;
* the second is `ComplexAnalytic.AnalyticSpace.Pullback.ι_comp_p2` and `h₂`, with nothing to
  cancel.

**The asymmetry is the open subspace and not the proof.** `p1` is read on a member as `toBase`,
which carries the inclusion of `Uᵢ` with it, and `p2` is read as the ambient second projection,
which does not. -/
theorem liftι_eq_liftMember (m : s.pt ⟶ glued U f g)
    (h₁ : m ≫ p1 U f g = s.fst) (h₂ : m ≫ p2 U f g = s.snd) (i : I) :
    liftι U f g i (s.pt.ofRestrict (conePreimage U f g s i) ≫ m)
        (range_base_ofRestrict_comp_subset_ι U f g s m h₁ i) =
      liftMember U f g s i := by
  have hfac := liftι_fac U f g i (s.pt.ofRestrict (conePreimage U f g s i) ≫ m)
    (range_base_ofRestrict_comp_subset_ι U f g s m h₁ i)
  have htoBase : liftι U f g i (s.pt.ofRestrict (conePreimage U f g s i) ≫ m)
        (range_base_ofRestrict_comp_subset_ι U f g s m h₁ i) ≫ toBase U f g i =
      s.pt.ofRestrict (conePreimage U f g s i) ≫ s.fst := by
    rw [← ι_comp_p1 U f g i, ← Category.assoc, hfac, Category.assoc, h₁]
  apply pullback.hom_ext
  · rw [liftMember_fst]
    refine (cancel_mono (X.ofRestrict (U i))).1 ?_
    rw [restrictHom_fac, Category.assoc]
    exact htoBase
  · rw [liftMember_snd, ← ι_comp_p2 U f g i, ← Category.assoc, hfac, Category.assoc, h₂]

variable (hU : ∀ x : X, ∃ i, x ∈ U i)

include hU in
/-- **The lift is unique** — the half of Mathlib's
`AlgebraicGeometry.Scheme.Pullback.gluedIsLimit` that `Oka/AnalyticSpace/PullbackGlue.lean` left
owed.

`ComplexAnalytic.AnalyticSpace.hom_ext_of_opens` over the preimage family reduces the equation to
one member at a time; there
`ComplexAnalytic.AnalyticSpace.Pullback.ofRestrict_comp_gluedLift` computes the right-hand side
and `ComplexAnalytic.AnalyticSpace.Pullback.liftι_eq_liftMember` together with
`…liftι_fac` computes the left-hand side to the same thing. **Both triangles are used and each is
used once**, in the two components of `…liftι_eq_liftMember`. -/
theorem gluedLift_uniq (m : s.pt ⟶ glued U f g)
    (h₁ : m ≫ p1 U f g = s.fst) (h₂ : m ≫ p2 U f g = s.snd) :
    m = gluedLift U f g s hU := by
  refine hom_ext_of_opens (conePreimage U f g s) (conePreimage_covers U f g s hU) fun i ↦ ?_
  rw [ofRestrict_comp_gluedLift, ← liftι_eq_liftMember U f g s m h₁ h₂ i,
    liftι_fac U f g i _ (range_base_ofRestrict_comp_subset_ι U f g s m h₁ i)]

/-! ### The limit cone, and the fibre product it gives -/

/-- **The gluing is the fibre product** — Mathlib's
`AlgebraicGeometry.Scheme.Pullback.gluedIsLimit`, over `ComplexAnalytic.AnalyticSpace`.

`CategoryTheory.Limits.PullbackCone.isLimitAux'` at the four declarations
`Oka/AnalyticSpace/PullbackGlue.lean` already had —
`ComplexAnalytic.AnalyticSpace.Pullback.p_comm` for the cone,
`…gluedLift` for the factorisation and `…gluedLift_p1`, `…gluedLift_p2` for its two triangles —
and `ComplexAnalytic.AnalyticSpace.Pullback.gluedLift_uniq` for the fifth thing, which is the
only one this file adds to that list. That file's own bullet predicted exactly this shape. -/
noncomputable def gluedIsLimit :
    IsLimit (PullbackCone.mk (p1 U f g) (p2 U f g) (p_comm U f g)) := by
  refine PullbackCone.isLimitAux' _ fun s ↦
    ⟨gluedLift U f g s hU, gluedLift_p1 U f g s hU, gluedLift_p2 U f g s hU, ?_⟩
  intro m h₁ h₂
  simp only [PullbackCone.mk_π_app] at h₁ h₂
  exact gluedLift_uniq U f g s hU m h₁ h₂

include hU in
/-- **The cospan has a fibre product** — Mathlib's
`AlgebraicGeometry.Scheme.Pullback.hasPullback_of_cover`, over `ComplexAnalytic.AnalyticSpace`.

**The hypotheses are the point and they are two.** The `U i` cover `X`, which is `hU`; and the
base change of `g` along each `Uᵢ ⟶ X ⟶ Z` already exists, which is the instance hypothesis this
file inherits from `Oka/AnalyticSpace/PullbackBlock.lean`. **Neither is discharged in this file**,
so nothing here gives `CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace`;
`Oka/AnalyticSpace/PullbackReduction.lean` discharges both and this theorem is what it discharges
them into, twice for a cover of a source and once for the cover of a base.

**This paragraph read *Neither is discharged anywhere in this repository for a general cospan*
until 2026-09-08**, and the words that replace it name this file rather than the tree, which is
what a sentence in a docstring can check of itself. -/
theorem hasPullback_of_cover : HasPullback f g :=
  ⟨⟨⟨_, gluedIsLimit U f g hU⟩⟩⟩

end ComplexAnalytic.AnalyticSpace.Pullback
