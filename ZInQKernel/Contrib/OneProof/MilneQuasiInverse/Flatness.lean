/-
ZInQKernel/Contrib/OneProof/MilneQuasiInverse/Flatness.lean

New code for this repository (not vendored).
Modified for the Z-in-Q kernel (milne-compile, fix 1): in `flat_of_kernelPair` an anonymous `have : IsAffine X`
shadowed the `wlog` hypothesis `this`; renamed `hXaff`. The flatness input of
`AvSplit.MilneIsogenyQuasiInverse`: a homomorphism of abelian varieties over any field whose
underlying morphism is finite and surjective is flat.

Route (no smoothness of `f`, no regularity, no miracle flatness, no algebraic closure):
1. In `Over (Spec K)`, the shear map `(a, a') ↦ (a, a⁻¹a')` identifies the kernel pair of
   `f.hom` with `A ×_K ker f` over the first factor (`isPullback_shear`); hence the first
   projection of the scheme-theoretic kernel pair of `f.hom.left` is a base change of the finite
   morphism `ker f → Spec K`, so it is finite, flat (over a field) and of constant rank
   (`kernelPair_fst_flat_finite_finrank`).
2. A finite surjective morphism onto a reduced scheme whose kernel pair has this property is flat
   (`flat_of_kernelPair`): reduce to `Spec S → Spec R` (Zariski-local on the target), where the
   statement is `RingFlatness.flat_of_rankAtStalk_tensor_self`.
3. `B` is reduced because it is geometrically integral over `K`.

Status: compiled by milne-compile on 2026-11-16 at Lean 4.35.0 / Mathlib v4.35.0 (one fix: a
shadowed `this` in `flat_of_kernelPair`, renamed `hXaff`). Written against the declarations of Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 read in source form (Morphisms/{Flat,Finite,FlatRank,
Basic,UnderlyingMap}, Pullbacks, PullbackCarrier, Properties, Geometrically/Integral, Scheme,
Monoidal/Cartesian/{Over,Mon,Grp}, Limits/Shapes/Pullback/{HasPullback,PullbackCone,IsPullback},
Limits/Constructions/Over/Connected, MorphismProperty/Limits). No proof
placeholders, no added axioms, no native evaluation, no reflection and no build-time code.
-/
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.RingFlatness
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.Tactic.Algebraize
import Mathlib.Tactic.WLOG

/-!
# Isogenies of abelian varieties are flat

Main result: `ZInQ.Contrib.MilneQuasiInverse.finite_surjective_abVarHom_flat`, for every field
`K`, abelian varieties `A B : PkgI3.AbVar K` and `f : PkgI3.AbVar.Hom A B` with
`PkgI3.AbVar.IsIsogenyMor f.hom`: `AlgebraicGeometry.Flat f.hom.left`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace ZInQ.Contrib.MilneQuasiInverse

universe u

/-! ## Kernel pairs under base change -/

section KernelPair

variable {X Y X' Y' : Scheme.{u}}

/-- The kernel pair of a base change is the base change of the kernel pair: for a pullback square
`b, φ', φ, g`, the square formed by the first projections of the kernel pairs over `b` is a
pullback square. -/
theorem isPullback_kernelPair_fst {φ : X ⟶ Y} {φ' : X' ⟶ Y'} {b : X' ⟶ X} {g : Y' ⟶ Y}
    (h : IsPullback b φ' φ g) :
    IsPullback (pullback.map φ' φ' φ φ b b g h.w.symm h.w.symm) (pullback.fst φ' φ')
      (pullback.fst φ φ) b := by
  have hm : pullback.map φ' φ' φ φ b b g h.w.symm h.w.symm ≫ pullback.snd φ φ =
      pullback.snd φ' φ' ≫ b := pullback.lift_snd _ _ _
  have hm' : pullback.map φ' φ' φ φ b b g h.w.symm h.w.symm ≫ pullback.fst φ φ =
      pullback.fst φ' φ' ≫ b := pullback.lift_fst _ _ _
  refine IsPullback.of_right ?_ hm' (IsPullback.of_hasPullback φ φ).flip
  rw [hm, h.w]
  exact (IsPullback.of_hasPullback φ' φ').flip.paste_horiz h

/-- Flatness, finiteness and constant rank of the first projection of the kernel pair pass to
base changes. -/
theorem kernelPair_fst_props_of_isPullback {φ : X ⟶ Y} {φ' : X' ⟶ Y'} {b : X' ⟶ X}
    {g : Y' ⟶ Y} (h : IsPullback b φ' φ g) (hfl : Flat (pullback.fst φ φ))
    (hfin : IsFinite (pullback.fst φ φ)) {N : ℕ}
    (hN : ∀ x, (pullback.fst φ φ).finrank x = N) :
    Flat (pullback.fst φ' φ') ∧ IsFinite (pullback.fst φ' φ') ∧
      ∀ x, (pullback.fst φ' φ').finrank x = N := by
  haveI := hfl
  haveI := hfin
  have sq := isPullback_kernelPair_fst h
  refine ⟨MorphismProperty.of_isPullback sq hfl, MorphismProperty.of_isPullback sq hfin,
    fun x => ?_⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq x]
  exact hN _

-- The two `backward.isDefEq` options below are the ones Mathlib itself sets for this pattern at
-- this pin: `Morphisms/Flat.lean` (the `IsZariskiLocalAtTarget.restrict` instance for `Flat` sets
-- `respectTransparency.types false`; the low-priority `Flat` instance using
-- `cancel_right_of_respectsIso @Flat` sets `respectTransparency false`) and
-- `Morphisms/FlatRank.lean` (`Scheme.Hom.one_le_finrank_iff_surjective`, whose
-- `wlog`/`iff_of_openCover`/`cancel_left_of_respectsIso` structure this proof follows). Without
-- them, synthesis of `IsZariskiLocalAtTarget @Flat` and `MorphismProperty.RespectsIso @Flat`
-- through the generic `HasRingHomProperty` instances fails. They only affect elaboration-time
-- unification; the kernel checks the resulting term as usual.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- **Flatness from the kernel pair.** A finite surjective morphism `φ : X ⟶ Y` onto a reduced
scheme is flat as soon as the first projection of its kernel pair is finite and flat of constant
rank. -/
theorem flat_of_kernelPair (φ : X ⟶ Y) [IsFinite φ] [Surjective φ]
    [AlgebraicGeometry.IsReduced Y] (hfl : Flat (pullback.fst φ φ))
    (hfin : IsFinite (pullback.fst φ φ)) (N : ℕ)
    (hN : ∀ x, (pullback.fst φ φ).finrank x = N) : Flat φ := by
  wlog hY : ∃ R, Y = Spec R generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @Flat) Y.affineCover]
    intro i
    dsimp only [Scheme.Cover.pullbackHom]
    obtain ⟨hfl', hfin', hN'⟩ := kernelPair_fst_props_of_isPullback
      (IsPullback.of_hasPullback φ (Y.affineCover.f i)) hfl hfin hN
    exact this (pullback.snd φ (Y.affineCover.f i)) hfl' hfin' hN' ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S generalizing X
  · have hXaff : IsAffine X := isAffine_of_isAffineHom φ
    rw [← MorphismProperty.cancel_left_of_respectsIso @Flat X.isoSpec.inv]
    have hsq : IsPullback X.isoSpec.inv (X.isoSpec.inv ≫ φ) φ (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩
    obtain ⟨hfl', hfin', hN'⟩ := kernelPair_fst_props_of_isPullback hsq hfl hfin hN
    exact this (X.isoSpec.inv ≫ φ) hfl' hfin' hN' ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective φ
  algebraize [ψ.hom]
  replace hfl : Flat (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) := hfl
  replace hfin : IsFinite (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) := hfin
  replace hN : ∀ x, (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))).finrank x = N := hN
  rw [← pullbackSpecIso_hom_fst' R S S] at hfl hfin hN
  rw [MorphismProperty.cancel_left_of_respectsIso @Flat] at hfl
  rw [MorphismProperty.cancel_left_of_respectsIso @IsFinite] at hfin
  haveI := hfl
  haveI := hfin
  rw [Scheme.Hom.finrank_comp_left_of_isIso] at hN
  haveI : Module.Flat S (S ⊗[R] S) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom, RingHom.flat_algebraMap_iff] at hfl
    exact hfl
  haveI : Module.Finite R S := (IsFinite.SpecMap_iff ψ).mp inferInstance
  haveI : _root_.IsReduced R := (affine_isReduced_iff R).mp inferInstance
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) :=
    (AlgebraicGeometry.surjective_iff (Spec.map ψ)).mp inferInstance
  have hrk : ∀ q : PrimeSpectrum S, Module.rankAtStalk (R := S) (S ⊗[R] S) q = N := fun q =>
    (Scheme.Hom.finrank_SpecMap_algebraMap S (S ⊗[R] S) q).symm.trans (hN q)
  have hflatRS : Module.Flat R S := RingFlatness.flat_of_rankAtStalk_tensor_self hsurj hrk
  rw [Flat.SpecMap_iff]
  exact (RingHom.flat_algebraMap_iff (R := R) (S := S)).mpr hflatRS

end KernelPair

/-! ## The shear isomorphism for a homomorphism of abelian varieties -/

section Shear

variable {K : Type} [Field K]

/-- The kernel of `f`: the pullback of `f.hom` along the unit `η[B.X]`, in `Over (Spec K)`. -/
abbrev kerOver {A B : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom A B) :
    Over (Spec (CommRingCat.of K)) :=
  pullback f.hom η[B.X]

/-- A point of the kernel maps to `1` under `f`. -/
theorem kerOver_condition {A B : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom A B)
    {T : Over (Spec (CommRingCat.of K))} (a : T ⟶ kerOver f) :
    (a ≫ pullback.fst f.hom η[B.X]) ≫ f.hom = 1 := by
  rw [Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def,
    toUnit_unique (a ≫ pullback.snd f.hom η[B.X]) (toUnit T)]

/-- The shear map `A ×_B A ⟶ ker f`, `(a, a') ↦ a⁻¹ a'`. -/
def shearMap {A B : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom A B) :
    pullback f.hom f.hom ⟶ kerOver f :=
  pullback.lift ((pullback.fst f.hom f.hom)⁻¹ * pullback.snd f.hom f.hom)
    (toUnit (pullback f.hom f.hom)) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, pullback.condition, inv_mul_cancel, Hom.one_def])

theorem shearMap_fst {A B : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom A B) :
    shearMap f ≫ pullback.fst f.hom η[B.X] =
      (pullback.fst f.hom f.hom)⁻¹ * pullback.snd f.hom f.hom :=
  pullback.lift_fst _ _ _

/-- **Shear.** The kernel pair of `f.hom`, with its first projection, is the product of `A.X` and
the kernel of `f`: the square `shearMap f, fst, (ker f ⟶ 𝟙_), (A.X ⟶ 𝟙_)` is a pullback square in
`Over (Spec K)`. -/
theorem isPullback_shear {A B : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom A B) :
    IsPullback (shearMap f) (pullback.fst f.hom f.hom) (pullback.snd f.hom η[B.X])
      (toUnit A.X) := by
  have w : shearMap f ≫ pullback.snd f.hom η[B.X] = pullback.fst f.hom f.hom ≫ toUnit A.X :=
    toUnit_unique _ _
  refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk w
    (fun s => pullback.lift s.snd (s.snd * (s.fst ≫ pullback.fst f.hom η[B.X]))
      (by rw [MonObj.mul_comp, kerOver_condition f s.fst, mul_one]))
    (fun s => ?_) (fun s => ?_) (fun s m h₁ h₂ => ?_))
  · apply pullback.hom_ext
    · rw [Category.assoc, shearMap_fst, MonObj.comp_mul, GrpObj.comp_inv, pullback.lift_fst,
        pullback.lift_snd, inv_mul_cancel_left]
    · exact toUnit_unique _ _
  · exact pullback.lift_fst _ _ _
  · apply pullback.hom_ext
    · rw [pullback.lift_fst, h₂]
    · rw [pullback.lift_snd, ← h₂, ← h₁, Category.assoc, shearMap_fst, MonObj.comp_mul,
        GrpObj.comp_inv, mul_inv_cancel_left]

/-- The shear square, on underlying schemes. -/
theorem isPullback_shear_left {A B : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom A B) :
    IsPullback (shearMap f).left (pullback.fst f.hom f.hom).left
      (pullback.snd f.hom η[B.X]).left A.X.hom :=
  (isPullback_shear f).map (Over.forget _)

/-- The kernel pair of `f.hom` in `Over (Spec K)` is a kernel pair of `f.hom.left`. -/
theorem isPullback_kernelPair_left {A B : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom A B) :
    IsPullback (pullback.fst f.hom f.hom).left (pullback.snd f.hom f.hom).left f.hom.left
      f.hom.left :=
  (IsPullback.of_hasPullback f.hom f.hom).map (Over.forget _)

/-- The kernel of `f`, on underlying schemes: a base change of `f.hom.left`. -/
theorem isPullback_kerOver_left {A B : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom A B) :
    IsPullback (pullback.fst f.hom η[B.X]).left (pullback.snd f.hom η[B.X]).left f.hom.left
      η[B.X].left :=
  (IsPullback.of_hasPullback f.hom η[B.X]).map (Over.forget _)

/-- The structure morphism `ker f ⟶ Spec K` on underlying schemes. -/
abbrev kerToSpec {A B : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom A B) :
    (kerOver f).left ⟶ Spec (CommRingCat.of K) :=
  (pullback.snd f.hom η[B.X]).left

/-- The first projection of the kernel pair of `f.hom.left` is finite and flat, of constant
rank. -/
theorem kernelPair_fst_flat_finite_finrank {A B : PkgI3.AbVar K} (f : PkgI3.AbVar.Hom A B)
    [IsFinite f.hom.left] :
    ∃ N : ℕ, Flat (pullback.fst f.hom.left f.hom.left) ∧
      IsFinite (pullback.fst f.hom.left f.hom.left) ∧
      ∀ x, (pullback.fst f.hom.left f.hom.left).finrank x = N := by
  haveI : IsFinite (kerToSpec f) :=
    MorphismProperty.of_isPullback (isPullback_kerOver_left f) ‹_›
  haveI : Flat (kerToSpec f) := inferInstance
  have hP := isPullback_kernelPair_left f
  have h1 : IsPullback hP.isoPullback.inv (pullback.fst f.hom.left f.hom.left)
      (pullback.fst f.hom f.hom).left (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [hP.isoPullback_inv_fst, Category.comp_id]⟩
  have sq : IsPullback (hP.isoPullback.inv ≫ (shearMap f).left)
      (pullback.fst f.hom.left f.hom.left) (kerToSpec f) A.X.hom := by
    have h2 := h1.paste_horiz (isPullback_shear_left f)
    rw [Category.id_comp] at h2
    exact h2
  refine ⟨(kerToSpec f).finrank default, MorphismProperty.of_isPullback sq inferInstance,
    MorphismProperty.of_isPullback sq inferInstance, fun x => ?_⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq x]
  congr 1
  exact Subsingleton.elim _ _

end Shear

/-! ## The export -/

/-- **Isogenies of abelian varieties are flat.** For every field `K`, abelian varieties
`A B : PkgI3.AbVar K` and a homomorphism `f : A → B` whose underlying morphism is finite and
surjective, `f.hom.left` is flat. -/
theorem finite_surjective_abVarHom_flat {K : Type} [Field K] {A B : PkgI3.AbVar K}
    (f : PkgI3.AbVar.Hom A B) (hf : PkgI3.AbVar.IsIsogenyMor f.hom) : Flat f.hom.left := by
  obtain ⟨hfin, hsurj⟩ := hf
  haveI : IsFinite f.hom.left := hfin
  haveI : Surjective f.hom.left := hsurj
  -- `B` is integral, hence reduced: it is geometrically integral over the one-point integral
  -- scheme `Spec K`. (`key` lets the codomain of `B.X.hom` be read as `Spec K` by unification.)
  have key : ∀ {S : Scheme.{0}} (g : B.X.left ⟶ S) [GeometricallyIntegral g] [Subsingleton S]
      [IsIntegral S], IsIntegral B.X.left :=
    fun g _ _ _ => GeometricallyIntegral.isIntegral_of_subsingleton g
  haveI : IsIntegral B.X.left :=
    @key (Spec (CommRingCat.of K)) B.X.hom B.geomInt inferInstance inferInstance
  obtain ⟨N, hfl, hfin', hN⟩ := kernelPair_fst_flat_finite_finrank f
  exact flat_of_kernelPair f.hom.left hfl hfin' N hN

end ZInQ.Contrib.MilneQuasiInverse
