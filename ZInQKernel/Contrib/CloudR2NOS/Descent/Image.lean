/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 scheme-only effective descent, route Q. This follows the Parent-approved plan
SCHEME_DESCENT_NATIVE_PLAN_001, sha 7a0aede9.

Sub-statements Q11–Q14, abstract form: the descended scheme is the scheme-theoretic image of
`X' → ℙ^M_S`, and cartesianness follows from flat base change of the kernel ideal sheaf.

NATIVE. SOURCE ONLY, UNCOMPILED. Universe u. The only option is autoImplicit false.

Suppliers:
* Mathlib `Scheme.IdealSheafData.comap`, `isPullback_of_isClosedImmersion`,
  `Scheme.Hom.{image, imageι, toImage, toImage_imageι, ker_comp_of_isIso, le_ker_comp}` and
  `Scheme.IdealSheafData.ker_subschemeι`;
* the published W07 `Scheme.Hom.ker_pullback_snd` (IdealSheaf/Image.lean, no numeric options);
* `IsPullback` pasting (`paste_horiz`, `of_right`).

Every statement is abstract: no FLT name occurs in this file. The concrete descent instances
are assembled in `Descent.Assembly`.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.IdealSheaf.Image

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Descent

/-- `Spec S' ⟶ Spec S` is flat for a flat algebra `S → S'`. -/
theorem flat_specMap_algebraMap (S S' : Type u) [CommRing S] [CommRing S'] [Algebra S S']
    [Module.Flat S S'] : Flat (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := by
  rw [HasRingHomProperty.Spec_iff (P := @Flat)]
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- **Q13, abstract form.** Precomposing with a split epimorphism leaves the kernel unchanged.

Truth check: `ker (a ≫ i) ⊇ ker i` always holds, and the reverse inclusion follows from
`ker (s ≫ a ≫ i) = ker i` because `s ≫ a = 𝟙`. -/
theorem ker_comp_of_comp_eq_id {X'' X' P : Scheme.{u}} (a : X'' ⟶ X') (s : X' ⟶ X'')
    (hs : s ≫ a = 𝟙 X') (i : X' ⟶ P) : (a ≫ i).ker = i.ker := by
  refine le_antisymm ?_ (Scheme.Hom.le_ker_comp a i)
  have h := Scheme.Hom.le_ker_comp s (a ≫ i)
  rwa [← Category.assoc, hs, Category.id_comp] at h

/-- **Q12, abstract form.** In a cartesian square along a flat `m`, with `c` quasi-compact, the
kernel of the base-changed map is the pulled-back kernel. This is the published W07
`Scheme.Hom.ker_pullback_snd`, transported along the comparison isomorphism. -/
theorem ker_eq_comap_of_isPullback {W X P' P : Scheme.{u}} {a : W ⟶ X} {b : W ⟶ P'}
    {c : X ⟶ P} {m : P' ⟶ P} (h : IsPullback a b c m) [QuasiCompact c] [Flat m] :
    b.ker = c.ker.comap m := by
  rw [← Scheme.Hom.ker_pullback_snd c m, ← h.isoPullback_hom_snd, Scheme.Hom.ker_comp_of_isIso]

/-- **Q14, abstract core.** Let `i` be a closed immersion into `P'` whose kernel is the pullback
along `m` of the kernel of `i ≫ m`. Then `i` is the base change along `m` of the closed
immersion of the scheme-theoretic image of `i ≫ m`. -/
theorem isPullback_toImage {X' P' P : Scheme.{u}} (i : X' ⟶ P') (m : P' ⟶ P)
    [IsClosedImmersion i] (hker : (i ≫ m).ker.comap m = i.ker) :
    IsPullback i (i ≫ m).toImage m (i ≫ m).imageι := by
  refine isPullback_of_isClosedImmersion i (i ≫ m).imageι (i ≫ m).toImage m
    (i ≫ m).toImage_imageι.symm ?_
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.ker_subschemeι]
  exact hker

/-- **Q11, abstract form.** The double overlap is the fibre product `X' ×_P P'`.

The data are:
* `hS : Spec(S'⊗S') = Spec S' ×_{Spec S} Spec S'`;
* `ha₁ : X'' = X' ×_{Spec S'} Spec(S'⊗S')`, via the first factor;
* `hf₂`, the commutativity of the second square;
* `i'` over `Spec S'`;
* `hP : P' = P ×_{Spec S} Spec S'`;
* the descent compatibility `hcomp` (Q10).

The conclusion is `IsPullback a₁ (a₂ ≫ i') (i' ≫ m) m`. -/
theorem isPullback_overlap {X' X'' T S₁ S₀ P' P : Scheme.{u}}
    {a₁ a₂ : X'' ⟶ X'} {f'' : X'' ⟶ T} {f' : X' ⟶ S₁} {ιL ιR : T ⟶ S₁} {ι : S₁ ⟶ S₀}
    (hS : IsPullback ιL ιR ι ι) (ha₁ : IsPullback a₁ f'' f' ιL) (hf₂ : a₂ ≫ f' = f'' ≫ ιR)
    {i' : X' ⟶ P'} {π' : P' ⟶ S₁} (hi' : i' ≫ π' = f') {m : P' ⟶ P} {π : P ⟶ S₀}
    (hP : IsPullback m π' π ι) (hcomp : a₁ ≫ i' ≫ m = a₂ ≫ i' ≫ m) :
    IsPullback a₁ (a₂ ≫ i') (i' ≫ m) m := by
  have big : IsPullback (f'' ≫ ιR) a₁ ι (f' ≫ ι) := ha₁.flip.paste_horiz hS.flip
  have e₁ : (a₂ ≫ i') ≫ π' = f'' ≫ ιR := by rw [Category.assoc, hi', hf₂]
  have e₂ : (i' ≫ m) ≫ π = f' ≫ ι := by rw [Category.assoc, hP.w, ← Category.assoc, hi']
  have big' : IsPullback ((a₂ ≫ i') ≫ π') a₁ ι ((i' ≫ m) ≫ π) := by
    rw [e₁, e₂]; exact big
  have p : (a₂ ≫ i') ≫ m = a₁ ≫ (i' ≫ m) := by
    rw [Category.assoc]; exact hcomp.symm
  exact (IsPullback.of_right big' p hP.flip).flip

/-- **Q14, cartesianness over the base.** Pasting `isPullback_toImage` with
`hP : P' = P ×_S S'` exhibits `X'` as `image ×_{Spec S} Spec S'`. -/
theorem isPullback_image_base {X' P' P S₁ S₀ : Scheme.{u}} (i : X' ⟶ P') (m : P' ⟶ P)
    [IsClosedImmersion i] (hker : (i ≫ m).ker.comap m = i.ker)
    {π' : P' ⟶ S₁} {π : P ⟶ S₀} {ι : S₁ ⟶ S₀} (hP : IsPullback m π' π ι)
    {f' : X' ⟶ S₁} (hi : i ≫ π' = f') :
    IsPullback (i ≫ m).toImage f' ((i ≫ m).imageι ≫ π) ι := by
  have h := (isPullback_toImage i m hker).paste_horiz hP.flip
  rw [hi] at h
  exact h.flip

/-- **Q14, coequaliser.** The two overlap projections agree after the map to the image,
because they agree after the closed immersion `imageι`, which is a monomorphism. -/
theorem comp_toImage_eq {X'' X' P' P : Scheme.{u}} (a₁ a₂ : X'' ⟶ X') (i : X' ⟶ P')
    (m : P' ⟶ P) (hcomp : a₁ ≫ i ≫ m = a₂ ≫ i ≫ m) :
    a₁ ≫ (i ≫ m).toImage = a₂ ≫ (i ≫ m).toImage := by
  rw [← cancel_mono (i ≫ m).imageι, Category.assoc, Category.assoc, (i ≫ m).toImage_imageι]
  exact hcomp

end ZInQ.Contrib.CloudR2NOS.Descent
