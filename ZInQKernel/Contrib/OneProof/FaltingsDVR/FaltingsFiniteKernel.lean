import ZInQKernel.Contrib.OneProof.MilneQuasiInverse.Kernel
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! A group scheme homomorphism with finite scheme-theoretic kernel is locally quasi-finite. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.MilneQuasiInverse.Kernel

set_option linter.style.haveILetI false

namespace ZInQ.FaltingsRestate

universe u

variable {S : Scheme.{u}} {X Y : Over S} [GrpObj X] [GrpObj Y]
variable (f : X ⟶ Y) [IsMonHom f]

private theorem finite_preimage_image_of_finite_kernel
    [IsFinite (kernelObject f).hom] (x : X.left) :
    (f.left ⁻¹' {f.left x}).Finite := by
  let T := Over.mk (X.left.fromSpecResidueField x ≫ X.hom)
  let r : T ⟶ X := Over.homMk (X.left.fromSpecResidueField x) rfl
  let K := kernelObject f
  let P := pullback (toUnit K) (toUnit T)
  let Q := pullback f (r ≫ f)
  let p : P ⟶ K := pullback.fst _ _
  let t : P ⟶ T := pullback.snd _ _
  let q : Q ⟶ X := pullback.fst _ _
  let t' : Q ⟶ T := pullback.snd _ _
  have hq : q ≫ f = (t' ≫ r) ≫ f := (pullback.condition (f := f) (g := r ≫ f)).trans
    (Category.assoc t' r f).symm
  have hp : (p ≫ kernelInclusion f) ≫ f = 1 := by
    rw [Category.assoc, kernelInclusion_comp, MonObj.comp_one]
  let a : P ⟶ Q := pullback.lift ((p ≫ kernelInclusion f) * (t ≫ r)) t (by
    rw [MonObj.mul_comp, hp, _root_.one_mul, Category.assoc])
  have ha₁ : a ≫ q = (p ≫ kernelInclusion f) * (t ≫ r) :=
    pullback.lift_fst _ _ _
  have ha₂ : a ≫ t' = t := pullback.lift_snd _ _ _
  have hker : (q * (t' ≫ r)⁻¹) ≫ f = 1 := by
    change pointsMap f Q (q * (t' ≫ r)⁻¹) = 1
    rw [map_mul, map_inv]
    change (q ≫ f) * ((t' ≫ r) ≫ f)⁻¹ = 1
    rw [hq, mul_inv_cancel]
  let qK : Q ⟶ K := (kernelPointsEquiv f Q).symm ⟨q * (t' ≫ r)⁻¹, hker⟩
  have hqK : qK ≫ kernelInclusion f = q * (t' ≫ r)⁻¹ := pullback.lift_fst _ _ _
  let b : Q ⟶ P := pullback.lift qK t' (Subsingleton.elim _ _)
  have hb₁ : b ≫ p = qK := pullback.lift_fst _ _ _
  have hb₂ : b ≫ t = t' := pullback.lift_snd _ _ _
  have hab : b ≫ a = 𝟙 Q := by
    apply pullback.hom_ext
    · change (b ≫ a) ≫ q = 𝟙 Q ≫ q
      rw [Category.assoc, ha₁, MonObj.comp_mul, ← Category.assoc b p,
        ← Category.assoc b t, hb₁, hb₂, hqK, inv_mul_cancel_right, Category.id_comp]
    · change (b ≫ a) ≫ t' = 𝟙 Q ≫ t'
      rw [Category.assoc, ha₂, hb₂, Category.id_comp]
  have hba : b.left ≫ a.left = 𝟙 Q.left := congrArg CommaMorphism.left hab
  haveI : Surjective a.left := ⟨fun z => ⟨b.left z, by
    rw [← Scheme.Hom.comp_apply, hba]
    rfl⟩⟩
  have ht : IsPullback p.left t.left K.hom T.hom := by
    change IsPullback p.left t.left (toUnit K).left (toUnit T).left
    exact (Over.forget S).map_isPullback (IsPullback.of_hasPullback _ _)
  haveI : IsFinite t.left := MorphismProperty.of_isPullback (P := @IsFinite) ht inferInstance
  haveI : Finite T.left := by
    change Finite (PrimeSpectrum (X.left.residueField x))
    infer_instance
  haveI : Finite P.left := by
    apply Set.finite_univ_iff.mp
    rw [← Set.preimage_univ (f := t.left)]
    exact t.left.finite_preimage Set.finite_univ
  haveI : Finite Q.left := Finite.of_surjective a.left a.left.surjective
  have hpb : IsPullback q.left t'.left f.left (r ≫ f).left :=
    (Over.forget S).map_isPullback (IsPullback.of_hasPullback f (r ≫ f))
  have hrg : Set.range (r ≫ f).left = {f.left x} := by
    change Set.range (X.left.fromSpecResidueField x ≫ f.left) = _
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.range_fromSpecResidueField, Set.image_singleton]
  have he : Set.range q.left = f.left ⁻¹' {f.left x} := by
    have he := Scheme.image_preimage_eq_of_isPullback hpb.flip
      (Set.univ : Set T.left)
    simpa only [Set.preimage_univ, Set.image_univ, hrg] using he
  rw [← he]
  exact Set.finite_range _

/-- A morphism of group schemes, locally of finite type and with finite
scheme-theoretic kernel, is locally quasi-finite. -/
theorem locallyQuasiFinite_of_finite_kernel
    [LocallyOfFiniteType f.left] [IsFinite (kernelObject f).hom] :
    LocallyQuasiFinite f.left := by
  apply LocallyQuasiFinite.of_finite_preimage_singleton
  intro y
  by_cases hy : y ∈ Set.range f.left
  · obtain ⟨x, rfl⟩ := hy
    exact finite_preimage_image_of_finite_kernel f x
  · have he : f.left ⁻¹' {y} = ∅ := by
      ext x
      change f.left x = y ↔ False
      exact iff_false_intro (fun hx => hy ⟨x, hx⟩)
    rw [he]
    exact Set.finite_empty

/-- Over a field it suffices that the kernel have finitely many underlying
scheme points. -/
theorem locallyQuasiFinite_of_finite_kernel_points
    {k : Type u} [Field k] {G H : Over (Spec (CommRingCat.of k))} [GrpObj G] [GrpObj H]
    (g : G ⟶ H) [IsMonHom g] [LocallyOfFiniteType g.left]
    [Finite (kernelObject g).left] : LocallyQuasiFinite g.left := by
  haveI : LocallyOfFiniteType (kernelObject g).hom := by
    rw [kernel_hom_eq_snd g]
    exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) (kernel_isPullback g) inferInstance
  haveI : LocallyQuasiFinite (kernelObject g).hom :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ fun _ => Set.toFinite _
  haveI : IsFinite (kernelObject g).hom := IsFinite.of_locallyQuasiFinite _
  exact locallyQuasiFinite_of_finite_kernel g

end ZInQ.FaltingsRestate
