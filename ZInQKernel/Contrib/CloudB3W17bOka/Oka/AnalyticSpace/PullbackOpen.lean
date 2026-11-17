/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.OpenSubspace
import Mathlib.Topology.LocalAtTarget

/-!
# The pullback of a morphism of complex analytic spaces along an open immersion

`Oka/AnalyticSpace/OpenSubspace.lean` builds the square

```
  X|f⁻¹V  --restrictHom f V-->  Y|V
     |                            |
 ofRestrict                  ofRestrict
     v                            v
     X  ---------- f ---------->  Y
```

and proves that it commutes, that a morphism into `X` whose image lies in `f⁻¹V` lifts, that the
lift is a factorisation, and that both vertical arrows are monomorphisms. **This file says that
the square is a pullback**, which is the sentence those four make and none of them states.

`ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict` is the instance that follows, so
`CategoryTheory.Limits.pullback` notation is usable at `ComplexAnalytic.AnalyticSpace` along a
leg of this shape.

## Why this is the shape that was reachable first, and the general one was not

**The heading read *Why this is the shape that is reachable and the general one is not* until
2026-09-08**, when `Oka/AnalyticSpace/PullbackReduction.lean` made
`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` a theorem by gluing over a
cover, which is the route the paragraph below names. Every measurement under this heading is
pinned to `e8c5f03` and none of them is retired by that; what was false was the present tense of
the heading itself.

At `e8c5f03`, and so at the Mathlib revision `lakefile.toml` pins there, neither
`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` nor
`CategoryTheory.Limits.HasBinaryProducts ComplexAnalytic.AnalyticSpace` synthesises, and the same
is true one category down: `CategoryTheory.Limits.HasPullbacks AlgebraicGeometry.LocallyRingedSpace`
does not synthesise either, and `Mathlib/Geometry/RingedSpace/LocallyRingedSpace/` carries a
`HasColimits` file and no limits file. **So the general fibre product cannot be got by taking it in
locally ringed spaces and checking the result is analytic**: there is nothing there to take, which
is why `Mathlib/AlgebraicGeometry/Pullbacks.lean` builds the fibre product of schemes by gluing
over an affine cover instead.

The one limit that does exist one category down is this one:
`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_left` and its locally-ringed-space
counterpart give the pullback along an open immersion as a restriction to a preimage. **This
repository already depended on that instance and had not stated it at the analytic level until
this file** — `Oka/AnalyticSpace/Glue.lean`'s gluing lemmas phrase their agreement hypothesis as an
equation of morphisms out of `CategoryTheory.Limits.pullback` of two members of an
`AlgebraicGeometry.LocallyRingedSpace.OpenCover`, which is exactly that pullback.

## Main results

- `ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict`: **the restriction square drawn at the top
  of this docstring is a pullback square.**
- `ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict` and
  `ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict'`: the two instances it gives, one for each
  order of the cospan.
- `ComplexAnalytic.AnalyticSpace.restrictIsoPullbackOfRestrict` and
  `ComplexAnalytic.AnalyticSpace.restrictIsoPullbackOfRestrict_hom_fst`: **that square read as an
  identification** — the pullback of `f` along the inclusion of `V` *is* the open subspace
  `X|f⁻¹V`, and the isomorphism carries the inclusion to `CategoryTheory.Limits.pullback.fst`.
  `CategoryTheory.Limits.HasPullback` is `Prop`-valued and keeps neither.
- `ComplexAnalytic.AnalyticSpace.hasPullback_pullbackFst_ofRestrict'`: **a pullback along a base
  change of an open-subspace inclusion, in the cospan order Mathlib's
  `CategoryTheory.IsPullback.instHasPullbackFst` does not reach.** The other order needs nothing
  from this repository and this file states no instance at it; the entry for the declaration says
  what was measured.
- `ComplexAnalytic.AnalyticSpace.pullback_condition_pullbackFst_ofRestrict`: that instance's
  commuting square, stated so that the tree fails to build rather than to guard green if instance
  search stops reaching it.
- `ComplexAnalytic.AnalyticSpace.isPullback_map_ofRestrict` and
  `ComplexAnalytic.AnalyticSpace.toLRSIsoPullbackMap`: **the same square, and the same pullback,
  one category down** — the forgetful functor to `AlgebraicGeometry.LocallyRingedSpace` carries
  the restriction square to a pullback square there, and the underlying locally ringed space of
  the analytic pullback is the pullback taken there.
- `ComplexAnalytic.AnalyticSpace.hasPullback_map_ofRestrict`: the instance that makes the second
  of those two statable, which is Mathlib's fact at the spelling a caller who has applied that
  functor holds.
- `ComplexAnalytic.AnalyticSpace.pullbackFst_eq_inv_comp_ofRestrict` and
  `ComplexAnalytic.AnalyticSpace.isOpenImmersion_map_pullbackFst_ofRestrict`: **the first
  projection *is* an open-subspace inclusion up to an isomorphism**, so its image downstairs is an
  open immersion of locally ringed spaces.
- `ComplexAnalytic.AnalyticSpace.range_base_pullbackFst_ofRestrict`: **and its image is the
  preimage of `V`.** The pair with the entry above is what a caller factoring a morphism through
  that projection needs — the first for a lift to exist, this for the range hypothesis that lift
  asks for.
- `ComplexAnalytic.AnalyticSpace.isPullback_pullbackFst_ofRestrict`,
  `ComplexAnalytic.AnalyticSpace.isPullback_map_pullbackFst_ofRestrict` and
  `ComplexAnalytic.AnalyticSpace.isPullback_map_pullback_pullbackFst_ofRestrict`: **the bridge at
  the cospan a glue datum's `t'` opens over**, whose two legs are
  `CategoryTheory.Limits.pullback.fst` at open-subspace inclusions rather than open-subspace
  inclusions themselves. The square there is a pullback square upstairs and downstairs with an
  *open subspace* as its apex, and the image of the analytic pullback square at that cospan is a
  pullback square too.
- `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom`: **a finite morphism restricted over an open
  subset of its target is finite**, with no hypothesis on the open subset.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_restrictHom`: the same for finite étale.
- `ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_ofRestrict`:
  `ComplexAnalytic.AnalyticSpace.isFiniteEtale_restrictHom` at the
  `CategoryTheory.Limits.pullback` spelling, which is
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`'s conclusion at this cospan.
  **This entry read *at the one cospan this category has a pullback over* until 2026-09-07**, when
  `Oka/AnalyticSpace/FiniteEtaleBaseChange.lean` and then
  `Oka/AnalyticSpace/CutOutFibreProduct.lean` gave the category further shapes. It was already
  false before the push that repaired it, which added no cospan of its own: a claim about the
  whole tree standing inside an entry about one declaration in this file.

## What this does not do

**It does not make `ComplexAnalytic.AnalyticSpace` a category with pullbacks, and it does not give
base change along a general morphism.** `Oka/AnalyticSpace/FiniteEtaleOver.lean`'s
`## What is not here` said that no `CategoryTheory.Limits.HasPullback` instance for analytic spaces
is available and that base change is therefore unstatable for `isFiniteEtale`; after this file the
first half of that was false as a universal and the second false at this one leg, and the sentences
there were narrowed to the general cospan rather than struck. The diagonal `A ⟶ A ×_B A` that a
monomorphism argument wants is over a cospan neither of whose legs is an open immersion, so nothing
here reaches it.

**This paragraph was in the present tense about that file until 2026-09-08**, when
`Oka/AnalyticSpace/PullbackReduction.lean` made
`CategoryTheory.Limits.HasPullbacks ComplexAnalytic.AnalyticSpace` a theorem and that bullet was
narrowed a second time, to the class and away from the limit; what this file did to it is what
this paragraph records and is unchanged, and the tense is what moved. **The first sentence is a
statement about *this* file and is untouched by any of it**: nothing declared below is that class,
which is what a `What this does not do` heading is for.

**And `ComplexAnalytic.AnalyticSpace.hasPullback_pullbackFst_ofRestrict'` adds no shape to the
accounting two other files keep.** `Oka/AnalyticSpace/ZeroLocus.lean` and
`Oka/AnalyticSpace/CutOutFibreProduct.lean` each quantify over cospans by whether a leg **is** the
inclusion of an open subspace, is finite étale, or is a morphism between local models presented by
cut-out data. **The second of the three read *is finite étale with Hausdorff
source* until 2026-09-14**, when the separation axiom came out of
`Oka/AnalyticSpace/FiniteEtaleBaseChange.lean`; the count of shapes is unmoved and so is every
figure in this paragraph. **This sentence
said *three other files* and named `Oka/AnalyticSpace/LocalIso.lean` first, until 2026-09-08**,
when that file retired its enumeration of shapes outright — an arbitrary cospan has a fibre
product, so it keeps no list of shapes to be a member of — and the count here follows it down.
`ComplexAnalytic.AnalyticSpace.restrictIsoPullbackOfRestrict_hom_fst` says that
`CategoryTheory.Limits.pullback.fst f (Y.ofRestrict V)` is
`ComplexAnalytic.AnalyticSpace.ofRestrict` of the preimage composed with an isomorphism of the
source, so the leg this file's new instance sits at is a leg of the **first** of those three
shapes up to that isomorphism, and no fourth shape appears. Both sentences are left alone for that
reason, and this paragraph is here rather than in them because it is a fact about declarations in
this file. **It read *Those three sentences* until 2026-09-08**, for the reason the record above
gives: the three shapes are still three and it is the files keeping the accounting that are two.

## The finiteness lemma and the one already here are not the same statement

`ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range` takes an embedding hypothesis
on the morphism and asks the open subset to sit inside its image, and gives finiteness of a
restriction of a morphism that is **not** finite — the open-immersion case its own docstring
describes. `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom` here takes finiteness of the
morphism and asks nothing of the open subset. Neither implies the other, and each is spent:
`isFinite_restrictHom_of_subset_range` in `Oka/Analytification/StandardEtaleFiniteness.lean`, and
this one in `ComplexAnalytic.AnalyticSpace.isFiniteEtale_restrictHom` below.
-/

open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace ComplexAnalytic.AnalyticSpace

variable {X Y : AnalyticSpace.{u}} (f : X ⟶ Y) (V : Y.Opens)

/-! ### The underlying map of a restriction -/

/-- **The base map of `ComplexAnalytic.AnalyticSpace.restrictHom` is `Set.restrictPreimage`.**

Both sides send a point of `f⁻¹V` to its image under `f`, seen in `V`; the equality is
`ComplexAnalytic.base_restrictHom` — the commuting square on points — read through `Subtype.ext`,
because the target's carrier is a subtype and its inclusion is `Subtype.val`.

**This is the bridge to `Mathlib/Topology/LocalAtTarget.lean`**, whose lemmas about a map restricted
over a subset of its target are all stated for `Set.restrictPreimage` and are unusable here without
it. `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom` consumes it, in both fields of
`ComplexAnalytic.AnalyticSpace.IsFinite`. -/
theorem base_restrictHom_eq_restrictPreimage :
    ((restrictHom f V).toLRSHom.base :
        X.restrict ((Opens.map f.toLRSHom.base).obj V) → Y.restrict V) =
      Set.restrictPreimage (V : Set Y) (f.toLRSHom.base : X → Y) :=
  funext fun x ↦ Subtype.ext (ComplexAnalytic.base_restrictHom f.toLRSHom V x)

/-! ### The square is a pullback -/

/-- **A cone over the cospan `f`, `ofRestrict V` maps into the preimage of `V`.**

This is the hypothesis `ComplexAnalytic.AnalyticSpace.liftRestrict` asks for, and it is the cone's
own commutation read at a point: the first leg followed by `f` and the second leg followed by the
inclusion of `V` agree, and the second lands in `V` by construction. Split out of
`ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict` below because the lift is a term whose
proof argument would otherwise be a tactic block inside a `refine`. -/
theorem range_subset_preimage_of_pullbackCone (s : PullbackCone f (Y.ofRestrict V)) :
    Set.range (s.fst.toLRSHom.base : s.pt → X) ⊆
      (((Opens.map f.toLRSHom.base).obj V : X.Opens) : Set X) := by
  rintro _ ⟨w, rfl⟩
  have h : (f.toLRSHom.base : X → Y) ((s.fst.toLRSHom.base : s.pt → X) w) =
      ((s.snd.toLRSHom.base : s.pt → Y.restrict V) w).1 :=
    congrArg (fun (φ : s.pt ⟶ Y) ↦ (φ.toLRSHom.base : s.pt → Y) w) s.condition
  simp only [Opens.map_coe, Set.mem_preimage, h]
  exact ((s.snd.toLRSHom.base : s.pt → Y.restrict V) w).2

/-- **The restriction of a morphism over an open subset of its target is a pullback square.**

Every ingredient is in `Oka/AnalyticSpace/OpenSubspace.lean` and nothing is constructed here:
`ComplexAnalytic.AnalyticSpace.restrictHom_fac` is the commuting square,
`ComplexAnalytic.AnalyticSpace.liftRestrict` is the lift and
`ComplexAnalytic.AnalyticSpace.liftRestrict_fac` its factorisation, and both halves of
uniqueness are cancellation against `ComplexAnalytic.AnalyticSpace.mono_ofRestrict`.

**The second factorisation is not proved directly and does not need to be.** A morphism into
`Y|V` is determined by its composite with the inclusion, because that inclusion is a
monomorphism, so `lift ≫ restrictHom f V = s.snd` follows from the outer square without ever
computing what the lift does to a point. -/
theorem isPullback_ofRestrict :
    IsPullback (X.ofRestrict ((Opens.map f.toLRSHom.base).obj V)) (restrictHom f V) f
      (Y.ofRestrict V) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (restrictHom_fac f V).symm
    (fun s ↦ liftRestrict s.fst _ (range_subset_preimage_of_pullbackCone f V s))
    (fun s ↦ liftRestrict_fac _ _ _) (fun s ↦ ?_) (fun s m hm _ ↦ ?_))
  · rw [← cancel_mono (Y.ofRestrict V), Category.assoc, restrictHom_fac,
      ← Category.assoc, liftRestrict_fac, s.condition]
  · rw [← cancel_mono (X.ofRestrict ((Opens.map f.toLRSHom.base).obj V)), liftRestrict_fac, hm]

/-- **A morphism of complex analytic spaces has a pullback along the inclusion of an open
subspace.** -/
instance hasPullback_ofRestrict : HasPullback f (Y.ofRestrict V) :=
  (isPullback_ofRestrict f V).hasPullback

/-- **The same cospan the other way round.** `CategoryTheory.IsPullback.flip` transposes the
square; the instance is stated separately because instance search matches the cospan's order and
not its transpose. -/
instance hasPullback_ofRestrict' : HasPullback (Y.ofRestrict V) f :=
  (isPullback_ofRestrict f V).flip.hasPullback

/-! ### That square read as an isomorphism, and the cospan orientation instance search misses -/

/-- **The pullback of `f` along the inclusion of `V` *is* the open subspace `X|f⁻¹V`**, as an
isomorphism against the `CategoryTheory.Limits.pullback` notation.

`ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict` says the restriction square is a pullback
square, and two limits over one cospan are uniquely isomorphic, so this is
`CategoryTheory.IsPullback.isoPullback` at it and there is nothing else in the proof. **What it
adds is what `CategoryTheory.Limits.HasPullback` discards**: that class is `Prop`-valued and so
keeps no identification of the limit with the object presenting it, so neither
`ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict` nor
`ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict'` carries one.

**The identification was already being used in this file, unnamed.**
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_ofRestrict` below writes
`(isPullback_ofRestrict f V).isoPullback` in a `haveI` and then rewrites with
`CategoryTheory.IsPullback.isoPullback_inv_snd`, which is a statement about that same
isomorphism. So this declaration names a term the file already spends rather than introducing
one, and that is the honest reason it is here; it is not needed by
`ComplexAnalytic.AnalyticSpace.hasPullback_pullbackFst_ofRestrict'`, whose proof does not mention
it. The move is `ComplexAnalytic.AnalyticSpace.fibreProdCutOutIsoPullback`'s at the fibre
product of local models, in a different spelling: there the two limits are compared by
`CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso`, here by
`CategoryTheory.IsPullback.isoPullback`, which is that comparison packaged for a square already
known to be a pullback. -/
noncomputable def restrictIsoPullbackOfRestrict :
    X.restrict ((Opens.map f.toLRSHom.base).obj V) ≅ pullback f (Y.ofRestrict V) :=
  (isPullback_ofRestrict f V).isoPullback

/-- **The isomorphism carries the open-subspace inclusion to `CategoryTheory.Limits.pullback.fst`.**

This is the half of `ComplexAnalytic.AnalyticSpace.restrictIsoPullbackOfRestrict` that says a base
change of the inclusion of an open subspace is again such an inclusion, and it is the half a caller
reading the notation back to `ComplexAnalytic.AnalyticSpace.ofRestrict` wants. The other half, over
`ComplexAnalytic.AnalyticSpace.restrictHom`, is not stated because nothing here consumes it. -/
@[simp]
theorem restrictIsoPullbackOfRestrict_hom_fst :
    (restrictIsoPullbackOfRestrict f V).hom ≫ pullback.fst f (Y.ofRestrict V) =
      X.ofRestrict ((Opens.map f.toLRSHom.base).obj V) :=
  (isPullback_ofRestrict f V).isoPullback_hom_fst

/-- **A morphism of complex analytic spaces has a pullback along the base change of an
open-subspace inclusion — in the order instance search does not already reach.**

The other order needs nothing from this repository. `CategoryTheory.IsPullback.instHasPullbackFst`
is Mathlib's, and at the revision `lakefile.toml` pins it reads
`[HasPullbacksAlong f] (h : P ⟶ Y) : HasPullback h (pullback.fst g f)`;
`CategoryTheory.Limits.HasPullbacksAlong` is a reducible `∀ {W} (h : W ⟶ Y), HasPullback h f`, so
`ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict` above already supplies it at
`Y.ofRestrict V`, and `HasPullback k (pullback.fst f (Y.ofRestrict V))` **synthesises in this
category with nothing added**. That is measured and not argued: `inferInstance` closes it at
`upstream/master` = `a84398c`, and this file states no instance at that cospan, because a
project-level copy of Mathlib's would be a duplicate.

Mathlib's instance is keyed on the *second* leg of the inner pullback and quantifies over the
first, and instance search matches a cospan's order and not its transpose, so this orientation is
the one shape it does not reach — measured at the same commit, where the statement below is
`failed to synthesize` without this declaration. `CategoryTheory.Limits.hasPullback_symmetry` is
the whole proof, and it consumes Mathlib's instance rather than anything here.

**The half of that which is a claim about Mathlib is measured away from this category**, in a file
whose only `import` is `Mathlib`, at `v4.32.0` — the revision `lakefile.toml` pins, resolved by
`lake-manifest.json` to `81a5d257c8e410db227a6665ed08f64fea08e997`. Under
`variable {C : Type*} [Category C] {P X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} [HasPullbacksAlong f]`
and `(h : P ⟶ Y)`, `#synth HasPullback h (pullback.fst g f)` prints
`IsPullback.instHasPullbackFst h` and `#synth HasPullback (pullback.fst g f) h` is `failed to
synthesize`. **The control is the positive one and the two lines differ only in the order of the
cospan**, so what the second measures is the orientation and not an absent limit: the objects,
the binders and the rev are the same in both. This is a claim about instance **synthesis**, which
no scan of source can decide — an instance stated at an arbitrary functor with some property would
carry this cospan without writing `pullback.fst` anywhere — and no `grep` was ever offered for it.

**The section heading above read *### That square read as an isomorphism, and the cospan
orientation Mathlib does not reach* until 2026-09-21**; `git show
c6bfc1f:Oka/AnalyticSpace/PullbackOpen.lean` carries it at `:242`. **It was a negative universal
about Mathlib in a section heading**, which is the one place this tree's rule for such a clause
cannot be met: a heading has no room for a version or an instrument, and taxis #2118 records that
a rule stated as a heading is not a rule. **Nothing quoted it**: `git grep` for the retired
heading over the tree at `c6bfc1f` returns that line and no other. The claim the heading made is
the one measured two paragraphs up, which is where it
belongs. -/
instance hasPullback_pullbackFst_ofRestrict' {T : AnalyticSpace.{u}} (k : T ⟶ X) :
    HasPullback (pullback.fst f (Y.ofRestrict V)) k :=
  hasPullback_symmetry _ _

/-- **The square over that cospan commutes**, which is
`CategoryTheory.Limits.pullback.condition` at it and carries no content of its own.

**It is stated so that something in the built tree fails to elaborate if
`ComplexAnalytic.AnalyticSpace.hasPullback_pullbackFst_ofRestrict'` stops being found.** A
`#print axioms` line on an instance records that instance's axioms and not that instance search
reaches it, so an instance sitting at a discrimination-tree key no search visits passes such a
guard and fails at every use site; this statement mentions
`CategoryTheory.Limits.pullback (pullback.fst f (Y.ofRestrict V)) k`, so it does not elaborate at
all unless that instance is **found**. Measured at `a84398c`: the statement fails to elaborate
without the instance above and elaborates with it. That seam is a recorded hazard in this corner
of the tree — `ComplexAnalytic.AnalyticSpace.isIso_stalkMap_ofRestrict`'s docstring exists for one
instance of it — and `ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_ofRestrict` below
carries the same double duty for `ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict`. -/
theorem pullback_condition_pullbackFst_ofRestrict {T : AnalyticSpace.{u}} (k : T ⟶ X) :
    pullback.fst (pullback.fst f (Y.ofRestrict V)) k ≫ pullback.fst f (Y.ofRestrict V) =
      pullback.snd (pullback.fst f (Y.ofRestrict V)) k ≫ k :=
  pullback.condition

/-! ### The same square one category down, and what a glue datum can take from it -/

/-- **The pullback of a morphism of locally ringed spaces along the inclusion of an open subspace,
at the spelling a caller of `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` holds.**

The mathematics is Mathlib's: the second leg is an open immersion and
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.hasPullback_of_right` supplies the limit.
What is added is a discrimination-tree key. Instance search reaches Mathlib's instance at
`AlgebraicGeometry.LocallyRingedSpace.ofRestrict` and does not reach it at
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace.map`, although the two terms are
`rfl`-equal — measured at `upstream/master` = `ebba2ce`, where the statement below is `failed to
synthesize` and its `ofRestrict`-spelled twin closes by `inferInstance`. That is the seam
`AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict`'s docstring is about, and its
prescription — an ascribed `haveI` at the spelling the goal uses — is the proof below.

**Why a global instance here and a `haveI` there.** That docstring argues against repairing the
instance graph and this declaration does repair it, at exactly one key and one class up. The
reason is `ComplexAnalytic.AnalyticSpace.toLRSIsoPullbackMap`, whose *type* names the pullback:
a call-site `haveI` cannot be reached during the elaboration of a type, so the instance a `def`
of that shape needs has to be global or the `def` cannot be stated. -/
instance hasPullback_map_ofRestrict :
    Limits.HasPullback (forgetToLocallyRingedSpace.map f)
      (forgetToLocallyRingedSpace.map (Y.ofRestrict V)) := by
  haveI : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (forgetToLocallyRingedSpace.map (Y.ofRestrict V)) :=
    AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict Y.toLocallyRingedSpace V
  infer_instance

/-- **The forgetful functor carries the restriction square to a pullback square of locally ringed
spaces.**

This is `AlgebraicGeometry.LocallyRingedSpace.isPullback_ofRestrict` at `f.toLRSHom`, with
`ComplexAnalytic.AnalyticSpace.restrictHom_fac` mapped down as the factorisation that theorem
takes as a hypothesis. Every `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace.map` in the
statement is `rfl`-equal to a `ComplexAnalytic.AnalyticSpace.Hom.toLRSHom`, and the square is
`rfl`-equal to the one that theorem is about; what the spelling buys is that the statement is
about the *image* of this file's square rather than about a square that happens to look like it.

**It does not follow from `ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict` and does not imply
it.** `ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` is faithful and not full — a
morphism of locally ringed spaces between analytic spaces need not be `ℂ`-linear, which is what
`ComplexAnalytic.IsCLinearHom` is in the definition of a morphism for — so a cone downstairs has
test objects and test morphisms the analytic statement never sees, and the analytic one is a
statement about a category this one says nothing about. **No claim is made here that the functor
preserves pullbacks**; what is proved is one square. -/
theorem isPullback_map_ofRestrict :
    CategoryTheory.IsPullback
      (forgetToLocallyRingedSpace.map (X.ofRestrict ((Opens.map f.toLRSHom.base).obj V)))
      (forgetToLocallyRingedSpace.map (restrictHom f V))
      (forgetToLocallyRingedSpace.map f)
      (forgetToLocallyRingedSpace.map (Y.ofRestrict V)) :=
  AlgebraicGeometry.LocallyRingedSpace.isPullback_ofRestrict f.toLRSHom V _
    (forgetToLocallyRingedSpace.congr_map (restrictHom_fac f V))

/-- **The underlying locally ringed space of the analytic pullback *is* the locally-ringed-space
pullback.**

Two comparisons composed, and neither is new:
`ComplexAnalytic.AnalyticSpace.restrictIsoPullbackOfRestrict` identifies the analytic pullback
with `X|f⁻¹V` upstairs, that identification is carried down by a
functor, and `ComplexAnalytic.AnalyticSpace.isPullback_map_ofRestrict` identifies `X|f⁻¹V` with
the pullback downstairs. **The content is that the second identification exists at all**, which is
`ComplexAnalytic.AnalyticSpace.isPullback_map_ofRestrict`.

**This is what a glue datum built out of analytic pieces needs.**
`Oka/AnalyticSpace/Glue.lean`'s entry points take an
`AlgebraicGeometry.LocallyRingedSpace.GlueData`, whose fields are locally ringed spaces and whose
`t'` is a morphism out of a pullback taken *there*; a pullback taken in
`ComplexAnalytic.AnalyticSpace` is not that object, and this isomorphism is what carries one to
the other. **It reaches one cospan and not every cospan**: the leg here is
`ComplexAnalytic.AnalyticSpace.ofRestrict`, and the cospan a glue datum's `t'` opens over has a
`CategoryTheory.Limits.pullback.fst` on each leg.
`ComplexAnalytic.AnalyticSpace.isPullback_map_pullback_pullbackFst_ofRestrict` at the foot of this
section reaches that cospan, as a `CategoryTheory.IsPullback` and not as an isomorphism: this file
states no `CategoryTheory.Limits.HasPullback` there, so a caller who wants the comparison supplies
that and applies `CategoryTheory.IsPullback.isoPullback`. **The cospan of two local models
presented by cut-out data is reached by neither**, and nothing in this file is about it.

**This paragraph closed *Whether the comparison is available there is not settled here and nothing
below claims it is* until 2026-09-08**, when
`ComplexAnalytic.AnalyticSpace.isPullback_map_pullback_pullbackFst_ofRestrict` settled that
cospan. It was exact when written. -/
noncomputable def toLRSIsoPullbackMap :
    (Limits.pullback f (Y.ofRestrict V)).toLocallyRingedSpace ≅
      Limits.pullback (forgetToLocallyRingedSpace.map f)
        (forgetToLocallyRingedSpace.map (Y.ofRestrict V)) :=
  (forgetToLocallyRingedSpace.mapIso (restrictIsoPullbackOfRestrict f V)).symm ≪≫
    (isPullback_map_ofRestrict f V).isoPullback

/-- **The first projection out of the pullback along an open-subspace inclusion is that inclusion
of the preimage, precomposed with an isomorphism.**

`ComplexAnalytic.AnalyticSpace.restrictIsoPullbackOfRestrict_hom_fst` says this with the
isomorphism on the other side; this is that equation solved for
`CategoryTheory.Limits.pullback.fst`, which is the form
`ComplexAnalytic.AnalyticSpace.isOpenImmersion_map_pullbackFst_ofRestrict` consumes and the form a
reader asking *what is this projection* wants. -/
theorem pullbackFst_eq_inv_comp_ofRestrict :
    Limits.pullback.fst f (Y.ofRestrict V) =
      (restrictIsoPullbackOfRestrict f V).inv ≫
        X.ofRestrict ((Opens.map f.toLRSHom.base).obj V) := by
  rw [← restrictIsoPullbackOfRestrict_hom_fst f V, Iso.inv_hom_id_assoc]

/-- **The image of that projection is an open immersion of locally ringed spaces.**

An isomorphism followed by the inclusion of an open subspace, by
`ComplexAnalytic.AnalyticSpace.pullbackFst_eq_inv_comp_ofRestrict`, and both survive
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace`.

**Stated as a theorem and not as an instance**, and the reason is
`AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict`'s: the remedy that file
prescribes for this seam is to wrap the fact and let a caller ascribe it in a `haveI` at the
spelling its goal uses, rather than to add a key to the instance graph. A caller who wants
`AlgebraicGeometry.LocallyRingedSpace.GlueData`'s open-immersion field at this leg does exactly
that. -/
theorem isOpenImmersion_map_pullbackFst_ofRestrict :
    AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (forgetToLocallyRingedSpace.map (Limits.pullback.fst f (Y.ofRestrict V))) := by
  haveI : AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
      (forgetToLocallyRingedSpace.map (X.ofRestrict ((Opens.map f.toLRSHom.base).obj V))) :=
    AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict X.toLocallyRingedSpace _
  rw [pullbackFst_eq_inv_comp_ofRestrict f V, forgetToLocallyRingedSpace.map_comp]
  infer_instance

/-- **And its image is the preimage of `V`.**

`ComplexAnalytic.AnalyticSpace.isOpenImmersion_map_pullbackFst_ofRestrict` says *that* the
projection is an open immersion; this says *where* it lands, and the two are the pair a caller
factoring a morphism through this projection needs — the first to have a lift at all, the second to
discharge the range hypothesis that lift asks for.

Both come off `ComplexAnalytic.AnalyticSpace.pullbackFst_eq_inv_comp_ofRestrict` and neither
recomputes anything: the isomorphism there is an isomorphism, so its underlying map is surjective
and contributes nothing to the image, and what is left is
`ComplexAnalytic.AnalyticSpace.range_base_ofRestrict`.

**The surjectivity is taken from `CategoryTheory.Iso.hom_inv_id` and not from an instance.** There
is no `Function.Surjective` instance on the base map of an isomorphism of analytic spaces at this
head, and the one line that produces it — evaluate `e.hom ≫ e.inv = 𝟙` at a point — is shorter
than the search for one would be. -/
theorem range_base_pullbackFst_ofRestrict :
    Set.range ((Limits.pullback.fst f (Y.ofRestrict V)).toLRSHom.base) =
      (f.toLRSHom.base : X → Y) ⁻¹' (V : Set Y) := by
  set e := restrictIsoPullbackOfRestrict f V with he
  have hsurj : Function.Surjective (e.inv.toLRSHom.base) :=
    fun y ↦ ⟨(e.hom.toLRSHom.base : _ → _) y,
      congrArg (fun (ψ : X.restrict ((Opens.map f.toLRSHom.base).obj V) ⟶
        X.restrict ((Opens.map f.toLRSHom.base).obj V)) ↦ (ψ.toLRSHom.base : _ → _) y) e.hom_inv_id⟩
  have hcomp : ((e.inv ≫ X.ofRestrict ((Opens.map f.toLRSHom.base).obj V)).toLRSHom.base :
        _ → X) =
      ((X.ofRestrict ((Opens.map f.toLRSHom.base).obj V)).toLRSHom.base : _ → X) ∘
        (e.inv.toLRSHom.base : _ → _) := rfl
  rw [pullbackFst_eq_inv_comp_ofRestrict f V, ← he, hcomp, Set.range_comp, hsurj.range_eq,
    Set.image_univ, range_base_ofRestrict]
  rfl

/-- **The `t'` cospan's square, with an open subspace as its apex.**

A glue datum's `t'` is a morphism out of a pullback over the cospan whose two legs are
`CategoryTheory.Limits.pullback.fst f (Y.ofRestrict V)` and
`CategoryTheory.Limits.pullback.fst f (Y.ofRestrict V')`, and
`ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict` does not reach it: neither leg is an
`ComplexAnalytic.AnalyticSpace.ofRestrict`. **What makes it reachable is that each leg *is* one up
to an isomorphism**, which is `ComplexAnalytic.AnalyticSpace.pullbackFst_eq_inv_comp_ofRestrict`,
so the cospan is an `ofRestrict` cospan transported along
`ComplexAnalytic.AnalyticSpace.restrictIsoPullbackOfRestrict` and `CategoryTheory.IsPullback` is
stable under that transport.

**Read the apex.** It is `X ×_Y V'` restricted to the preimage of `f ⁻¹ V` — an open subspace of
the object the second leg comes out of, and not a chosen limit, which is what a
`AlgebraicGeometry.LocallyRingedSpace.GlueData`'s `V (i, j)` has to be if a hypothesis about it is
to be discharged by the tools that discharge hypotheses about spaces one can name.
`AlgebraicGeometry.LocallyRingedSpace.restrictInfIsoPullback`'s docstring gives that reason for
its own existence. -/
theorem isPullback_pullbackFst_ofRestrict (V' : Y.Opens) :
    IsPullback
      (restrictHom (Limits.pullback.fst f (Y.ofRestrict V'))
          ((Opens.map f.toLRSHom.base).obj V) ≫ (restrictIsoPullbackOfRestrict f V).hom)
      ((Limits.pullback f (Y.ofRestrict V')).ofRestrict
        ((Opens.map (Limits.pullback.fst f (Y.ofRestrict V')).toLRSHom.base).obj
          ((Opens.map f.toLRSHom.base).obj V)))
      (Limits.pullback.fst f (Y.ofRestrict V)) (Limits.pullback.fst f (Y.ofRestrict V')) := by
  rw [pullbackFst_eq_inv_comp_ofRestrict f V]
  exact (isPullback_ofRestrict (Limits.pullback.fst f (Y.ofRestrict V'))
      ((Opens.map f.toLRSHom.base).obj V)).flip.of_iso (Iso.refl _)
    (restrictIsoPullbackOfRestrict f V) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

/-- **The same square one category down**, with the same open subspace as its apex.

The proof is `ComplexAnalytic.AnalyticSpace.isPullback_pullbackFst_ofRestrict`'s read one category
down, with `ComplexAnalytic.AnalyticSpace.isPullback_map_ofRestrict` in place of the analytic
square. It does **not** follow from the analytic statement — nothing here says
`ComplexAnalytic.AnalyticSpace.forgetToLocallyRingedSpace` preserves this or any limit, and the
paragraph on `ComplexAnalytic.AnalyticSpace.isPullback_map_ofRestrict` says why it cannot be
assumed to.

**No lemma of this repository is used for the transport.** `CategoryTheory.IsPullback.of_iso` is
Mathlib's, at the pinned revision, and it takes isomorphisms of all four objects; the three
identities and one isomorphism it is applied to here are what specialise it to replacing the
source of a single leg. -/
theorem isPullback_map_pullbackFst_ofRestrict (V' : Y.Opens) :
    IsPullback
      (forgetToLocallyRingedSpace.map
        (restrictHom (Limits.pullback.fst f (Y.ofRestrict V'))
            ((Opens.map f.toLRSHom.base).obj V) ≫ (restrictIsoPullbackOfRestrict f V).hom))
      (forgetToLocallyRingedSpace.map
        ((Limits.pullback f (Y.ofRestrict V')).ofRestrict
          ((Opens.map (Limits.pullback.fst f (Y.ofRestrict V')).toLRSHom.base).obj
            ((Opens.map f.toLRSHom.base).obj V))))
      (forgetToLocallyRingedSpace.map (Limits.pullback.fst f (Y.ofRestrict V)))
      (forgetToLocallyRingedSpace.map (Limits.pullback.fst f (Y.ofRestrict V'))) := by
  rw [forgetToLocallyRingedSpace.map_comp,
    show forgetToLocallyRingedSpace.map (Limits.pullback.fst f (Y.ofRestrict V)) =
      (forgetToLocallyRingedSpace.mapIso (restrictIsoPullbackOfRestrict f V)).inv ≫
        forgetToLocallyRingedSpace.map (X.ofRestrict ((Opens.map f.toLRSHom.base).obj V)) from by
      rw [Functor.mapIso_inv, ← forgetToLocallyRingedSpace.map_comp,
        ← pullbackFst_eq_inv_comp_ofRestrict f V]]
  exact (isPullback_map_ofRestrict (Limits.pullback.fst f (Y.ofRestrict V'))
      ((Opens.map f.toLRSHom.base).obj V)).flip.of_iso (Iso.refl _)
    (forgetToLocallyRingedSpace.mapIso (restrictIsoPullbackOfRestrict f V))
    (Iso.refl _) (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

/-- **The forgetful functor carries the analytic pullback square at the `t'` cospan to a pullback
square.**

`ComplexAnalytic.AnalyticSpace.isPullback_pullbackFst_ofRestrict` and
`ComplexAnalytic.AnalyticSpace.isPullback_map_pullbackFst_ofRestrict` are about a square whose
apex is an open subspace; this is the same square with that apex replaced by
`CategoryTheory.Limits.pullback` of the two legs, which exists
by `ComplexAnalytic.AnalyticSpace.hasPullback_pullbackFst_ofRestrict'`. The isomorphism between
them is the analytic square's own
`CategoryTheory.IsPullback.isoPullback`, carried down by the functor, and
`CategoryTheory.IsPullback.of_iso` transports the statement along it.

**This is what taxis #1871's second obstruction asked for.** A glue datum's `t'` maps between
pullbacks taken in the datum's own category, and the analytic pullback at this cospan is not that
object; this says the image of the analytic one *is* a pullback there, so a caller holding
`CategoryTheory.Limits.HasPullback` downstairs gets the comparison from
`CategoryTheory.IsPullback.isoPullback`. **This file adds no instance at that key** — the seam
`ComplexAnalytic.AnalyticSpace.isOpenImmersion_map_pullbackFst_ofRestrict`'s docstring is about,
one class up, and the remedy it prescribes is an ascribed `haveI` at the caller.

**It does not reach taxis #1871's first obstruction**, which is the larger one: the ambient pieces
of Mathlib's glue datum are pullbacks over a cospan of local models presented by cut-out data,
neither of whose legs is an `ComplexAnalytic.AnalyticSpace.ofRestrict`, and no declaration of
`Oka/AnalyticSpace/PullbackOpen.lean` says anything about them. -/
theorem isPullback_map_pullback_pullbackFst_ofRestrict (V' : Y.Opens) :
    IsPullback
      (forgetToLocallyRingedSpace.map
        (Limits.pullback.fst (Limits.pullback.fst f (Y.ofRestrict V))
          (Limits.pullback.fst f (Y.ofRestrict V'))))
      (forgetToLocallyRingedSpace.map
        (Limits.pullback.snd (Limits.pullback.fst f (Y.ofRestrict V))
          (Limits.pullback.fst f (Y.ofRestrict V'))))
      (forgetToLocallyRingedSpace.map (Limits.pullback.fst f (Y.ofRestrict V)))
      (forgetToLocallyRingedSpace.map (Limits.pullback.fst f (Y.ofRestrict V'))) := by
  refine (isPullback_map_pullbackFst_ofRestrict f V V').of_iso
    (forgetToLocallyRingedSpace.mapIso (isPullback_pullbackFst_ofRestrict f V V').isoPullback)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id,
      ← forgetToLocallyRingedSpace.map_comp]
    exact congrArg _ (isPullback_pullbackFst_ofRestrict f V V').isoPullback_hom_fst.symm
  · simp only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id,
      ← forgetToLocallyRingedSpace.map_comp]
    exact congrArg _ (isPullback_pullbackFst_ofRestrict f V V').isoPullback_hom_snd.symm

/-! ### Base change along an open immersion -/

/-- **A finite morphism restricted over an open subset of its target is finite**, and nothing is
asked of the open subset.

Both fields of `ComplexAnalytic.AnalyticSpace.IsFinite` survive:

* the base map is closed by `IsClosedMap.restrictPreimage`, which restricts a closed map over an
  arbitrary subset of the target — the witness for a closed set upstairs being the image of its
  closure — reached through
  `ComplexAnalytic.AnalyticSpace.base_restrictHom_eq_restrictPreimage`;
* a fibre of the restriction sits inside a fibre of the morphism, by the inclusion of the
  preimage, and an injection into a finite type has finite source.

**This is a different statement from
`ComplexAnalytic.AnalyticSpace.isFinite_restrictHom_of_subset_range`**, whose hypotheses are on the
base map and on the open subset and whose conclusion is about a morphism that is not finite; see
this file's header. -/
instance isFinite_restrictHom [IsFinite f] : IsFinite (restrictHom f V) where
  isClosedMap := by
    rw [base_restrictHom_eq_restrictPreimage]
    exact (IsFinite.isClosedMap (f := f)).restrictPreimage _
  finite_fiber y := by
    have hset : ((restrictHom f V).toLRSHom.base : _ → Y.restrict V) ⁻¹' {y} =
        Subtype.val ⁻¹' ((f.toLRSHom.base : X → Y) ⁻¹' {y.1}) := by
      rw [base_restrictHom_eq_restrictPreimage]
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact Subtype.ext_iff
    rw [hset]
    have hfib : Finite ((f.toLRSHom.base : X → Y) ⁻¹' {y.1}) := IsFinite.finite_fiber _
    exact Finite.of_injective
      (fun x ↦ (⟨x.1.1, x.2⟩ : ((f.toLRSHom.base : X → Y) ⁻¹' {y.1} : Set X)))
      (by
        intro a b h
        simp only [Subtype.mk.injEq] at h
        exact Subtype.ext (Subtype.ext h))

/-- **A finite étale morphism restricted over an open subset of its target is finite étale.**

The two fields are `ComplexAnalytic.AnalyticSpace.isFinite_restrictHom` above and
`ComplexAnalytic.AnalyticSpace.isLocalIso_restrictHom`, which was already in
`Oka/AnalyticSpace/OpenSubspace.lean` and asks nothing of the open subset either.

**Read with `ComplexAnalytic.AnalyticSpace.isPullback_ofRestrict`, this is base change of
`ComplexAnalytic.AnalyticSpace.isFiniteEtale` along an open immersion**: the restriction is the
pullback, so the pullback of a finite étale morphism along the inclusion of an open subspace is
finite étale. It is not `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`, which
quantifies over every cospan and asks for the class across each of them; that class is
`ComplexAnalytic.AnalyticSpace.isStableUnderBaseChange_isFiniteEtale`, in
`Oka/AnalyticSpace/FiniteEtaleStableUnderBaseChange.lean`, which is assembled from
`ComplexAnalytic.AnalyticSpace.isFiniteEtale_pullback_snd_of_isFiniteEtale` and not from this
instance — **this statement asks nothing of the open subset and is not a consequence of that
class**, since it reaches the restriction rather than a chosen pullback. **The clause closing this
sentence read *and needs a fibre product this category does
not have* until 2026-09-08**, when `Oka/AnalyticSpace/PullbackReduction.lean` gave the category
`ComplexAnalytic.AnalyticSpace.hasPullbacks`: the limit is there and the class carried across it is
what is not, which is the narrowing
`Oka/AnalyticSpace/FiniteEtaleOver.lean`'s bullet took on the same day. **And the sentence read
*`Oka/AnalyticSpace/FiniteEtaleOver.lean`'s `## No base change of the class over a general cospan`
bullet is where that absence is stated and measured, and this sentence defers to it rather than
restating it* until 2026-09-15**, when the class stopped being an absence and that bullet was
re-headed **No base change of the class over a cospan of morphisms of covers**, which is about a
different category and is not what this sentence was deferring to. -/
instance isFiniteEtale_restrictHom [IsFiniteEtale f] : IsFiniteEtale (restrictHom f V) where
  isFinite := isFinite_restrictHom f V
  isLocalIso := isLocalIso_restrictHom f V

/-- **The base change of a finite étale morphism along the inclusion of an open subspace is finite
étale**, written at the `CategoryTheory.Limits.pullback` spelling rather than at the restriction.

This is `ComplexAnalytic.AnalyticSpace.isFiniteEtale_restrictHom` transported along
`CategoryTheory.IsPullback.isoPullback`, whose `isoPullback_inv_snd` says the second projection
out of the chosen pullback is that isomorphism followed by
`ComplexAnalytic.AnalyticSpace.restrictHom`; being finite étale then survives the composite because
an isomorphism is finite étale and the class is closed under composition.

**It is stated because the restriction spelling and the `pullback` spelling are not
interchangeable to instance search**, and a caller who writes a square rather than a preimage holds
the second. It is also what shows `ComplexAnalytic.AnalyticSpace.hasPullback_ofRestrict` is
*found* and not merely present: the statement cannot be written at all unless that instance is
synthesised. -/
instance isFiniteEtale_pullback_snd_ofRestrict [IsFiniteEtale f] :
    IsFiniteEtale (Limits.pullback.snd f (Y.ofRestrict V)) := by
  haveI : IsFiniteEtale (isPullback_ofRestrict f V).isoPullback.inv :=
    isFiniteEtale_of_isIso _
  rw [← (isPullback_ofRestrict f V).isoPullback_inv_snd]
  infer_instance

end ComplexAnalytic.AnalyticSpace
