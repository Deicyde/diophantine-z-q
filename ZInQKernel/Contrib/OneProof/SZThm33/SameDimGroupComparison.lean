import ZInQKernel.Contrib.OneProof.FaltingsDVR.FaltingsFiniteKernel
import ZInQKernel.Contrib.Dim.FunctionField
import Mathlib.FieldTheory.FinTrdeg

/-! A dominant group homomorphism of equal-dimensional integral algebraic
groups has finite kernel. The generic fibre calculation extends Jack McCarthy's
proof in `OneProof/SameDimFinite.lean` from surjections of abelian varieties
to dominant homomorphisms of algebraic groups. -/

noncomputable section

set_option linter.style.haveILetI false

namespace SZRaynaud

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace
open ZInQ.Contrib.Dim
open ZInQ.Contrib.MilneQuasiInverse.Kernel

section GenericFibre

variable {k : Type} [Field k] {X Y : Scheme.{0}}

private theorem genericPoint_map (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  apply IsGenericPoint.eq _ (genericPoint_spec Y)
  simpa only [Set.image_univ, f.denseRange.closure_eq] using
    (genericPoint_spec X).image f.continuous

/-- The canonical point of `X` over its function field respects the structure map to `Spec k`. -/
private theorem fromSpecStalk_generic_comp [IsIntegral X] (a : X ⟶ Spec (CommRingCat.of k)) :
    letI := functionFieldAlgebra k X a
    X.fromSpecStalk (genericPoint X) ≫ a =
      Spec.map (CommRingCat.ofHom (algebraMap k X.functionField)) := by
  change X.fromSpecStalk (genericPoint X) ≫ a =
    Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ a.appTop ≫ X.germToFunctionField ⊤)
  rw [Spec.map_comp, Spec.map_comp, ← X.fromSpecStalk_toSpecΓ]
  simp only [Category.assoc, ← Scheme.toSpecΓ_naturality_assoc,
    toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

private theorem functionField_essFiniteType [IsIntegral X] (a : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType a] :
    letI := functionFieldAlgebra k X a
    Algebra.EssFiniteType k X.functionField := by
  let := functionFieldAlgebra k X a
  let x := genericPoint X
  have h : IsLocalRing.closedPoint k = a x := Subsingleton.elim _ _
  let e := (Spec (CommRingCat.of k)).presheaf.stalkCongr (.of_eq h.symm) ≪≫
    stalkClosedPointIso (CommRingCat.of k)
  have he : Spec.map e.inv = (Spec (CommRingCat.of k)).fromSpecStalk (a x) := by
    rw [Iso.trans_inv, Spec.map_comp, Spec_stalkClosedPointIso]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (specializes_of_eq h.symm)
  have hm : CommRingCat.ofHom (algebraMap k X.functionField) = e.inv ≫ a.stalkMap x := by
    apply Spec.map_injective
    rw [← fromSpecStalk_generic_comp a, Spec.map_comp, he,
      Scheme.SpecMap_stalkMap_fromSpecStalk]
  rw [← RingHom.essFiniteType_algebraMap]
  change (CommRingCat.ofHom (algebraMap k X.functionField)).hom.EssFiniteType
  rw [hm, CommRingCat.hom_comp, RingHom.EssFiniteType.respectsIso.cancel_left_isIso]
  exact LocallyOfFiniteType.stalkMap a x

/-- A dominant map between equal-dimensional integral schemes of finite type over a field is
quasi-finite at the generic point of the source. -/
private theorem quasiFiniteAt_generic_of_sameDim [IsIntegral X] [IsIntegral Y]
    (a : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType a]
    (b : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [IsDominant f] [LocallyOfFiniteType f] (hab : f ≫ b = a)
    (hd : topologicalKrullDim X = topologicalKrullDim Y) :
    f.QuasiFiniteAt (genericPoint X) := by
  let x := genericPoint X
  let y := genericPoint Y
  have hxy : f x = y := genericPoint_map f
  let e := Y.presheaf.stalkCongr (.of_eq hxy.symm)
  let φ : Y.functionField ⟶ X.functionField := e.hom ≫ f.stalkMap x
  let := functionFieldAlgebra k X a
  let := functionFieldAlgebra k Y b
  let : Algebra Y.functionField X.functionField := φ.hom.toAlgebra
  have hφ : Spec.map φ ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ f := by
    rw [Spec.map_comp, Category.assoc]
    have he : Spec.map e.hom ≫ Y.fromSpecStalk y = Y.fromSpecStalk (f x) :=
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk (specializes_of_eq hxy)
    rw [he, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have : IsScalarTower k Y.functionField X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    have h : CommRingCat.ofHom (algebraMap k X.functionField) =
        CommRingCat.ofHom (algebraMap k Y.functionField) ≫ φ := by
      apply Spec.map_injective
      rw [← fromSpecStalk_generic_comp a, Spec.map_comp, ← fromSpecStalk_generic_comp b,
        ← Category.assoc, hφ, Category.assoc, hab]
    exact congrArg CommRingCat.Hom.hom h
  have := functionField_essFiniteType a
  have := functionField_essFiniteType b
  have htr : Algebra.trdeg k X.functionField = Algebra.trdeg k Y.functionField := by
    rw [topologicalKrullDim_eq_trdeg_functionField k X a,
      topologicalKrullDim_eq_trdeg_functionField k Y b] at hd
    apply Cardinal.toENat_injOn (x₁ := Algebra.trdeg k X.functionField)
      (x₂ := Algebra.trdeg k Y.functionField)
      (trdeg_lt_aleph0 k X.functionField).le (trdeg_lt_aleph0 k Y.functionField).le
    exact WithBot.coe_injective hd
  have : Algebra.IsAlgebraic Y.functionField X.functionField := by
    apply trdeg_eq_zero_iff.mp
    have ht := trdeg_add_eq k Y.functionField (A := X.functionField)
    rw [htr] at ht
    exact (Cardinal.add_eq_left_iff.mp ht).resolve_left fun h =>
      (not_le_of_gt (trdeg_lt_aleph0 k Y.functionField)) ((le_max_left _ _).trans h)
  have : Algebra.EssFiniteType Y.functionField X.functionField :=
    Algebra.EssFiniteType.of_comp k _ _
  have hf : φ.hom.Finite := Algebra.finite_of_essFiniteType_of_isAlgebraic
  have hq := RingHom.QuasiFinite.of_finite hf
  exact (RingHom.QuasiFinite.respectsIso.cancel_left_isIso e.hom (f.stalkMap x)).mp hq

/-- A generic point isolated in its fibre is the only point of that fibre. -/
private theorem subsingleton_genericFiber [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [LocallyOfFiniteType f] (hq : f.QuasiFiniteAt (genericPoint X)) :
    Subsingleton (f.fiber (genericPoint Y)) := by
  rw [← genericPoint_map f]
  let x := genericPoint X
  have hc := hq.isClopen_singleton_asFiber.1
  have he (p : f.fiber (f x)) : p = f.asFiber x := by
    have hsp : f.asFiber x ⤳ p := by
      apply (f.fiberHomeo (f x)).isEmbedding.isInducing.specializes_iff.mp
      apply (subtype_specializes_iff _ _).mpr
      rw [Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberι_asFiber]
      exact (genericPoint_spec X).specializes trivial
    exact Set.mem_singleton_iff.mp (hsp.mem_closed hc (Set.mem_singleton _))
  exact ⟨fun p q => (he p).trans (he q).symm⟩

/-- A quasi-compact map with a single-point generic fibre has a finite generic fibre. -/
private theorem finite_genericFiber [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [LocallyOfFiniteType f] [QuasiCompact f] (hq : f.QuasiFiniteAt (genericPoint X)) :
    IsFinite (f.fiberToSpecResidueField (genericPoint Y)) := by
  have := subsingleton_genericFiber f hq
  let g := f.fiberToSpecResidueField (genericPoint Y)
  have : LocallyOfFiniteType g := inferInstanceAs (LocallyOfFiniteType (pullback.snd f _))
  have : QuasiCompact g := inferInstanceAs (QuasiCompact (pullback.snd f _))
  have : LocallyQuasiFinite g := LocallyQuasiFinite.of_finite_preimage_singleton g
    (fun _ => Set.toFinite _)
  exact IsFinite.of_locallyQuasiFinite g

/-- A fibre over a field-valued generic point is a base change of the generic fibre. -/
private theorem finite_geometricGenericFiber [IsIntegral Y] {L : Type} [Field L]
    (f : X ⟶ Y) (b : Spec (CommRingCat.of L) ⟶ Y)
    (hb : b (IsLocalRing.closedPoint L) = genericPoint Y)
    [IsFinite (f.fiberToSpecResidueField (genericPoint Y))] :
    IsFinite (pullback.snd f b) := by
  obtain ⟨⟨y, p⟩, rfl⟩ := (Scheme.SpecToEquivOfField L Y).symm.surjective b
  change Y.fromSpecResidueField y (Spec.map p (IsLocalRing.closedPoint L)) = _ at hb
  rw [Scheme.fromSpecResidueField_apply] at hb
  subst y
  change IsFinite (pullback.snd f (Spec.map p ≫ Y.fromSpecResidueField (genericPoint Y)))
  have hf : IsFinite (pullback.snd (f.fiberToSpecResidueField (genericPoint Y)) (Spec.map p)) :=
    inferInstance
  change IsFinite (pullback.snd (pullback.snd f (Y.fromSpecResidueField (genericPoint Y)))
    (Spec.map p)) at hf
  let e := pullbackLeftPullbackSndIso f (Y.fromSpecResidueField (genericPoint Y)) (Spec.map p)
  let g := pullback.snd f (Spec.map p ≫ Y.fromSpecResidueField (genericPoint Y))
  have : IsFinite (e.hom ≫ g) := by
    simpa only [e, g, pullbackLeftPullbackSndIso_hom_snd] using hf
  have hcomp : IsFinite (e.inv ≫ e.hom ≫ g) := inferInstance
  simpa only [Iso.inv_hom_id_assoc] using hcomp

end GenericFibre

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of a dominant morphism of equal-dimensional integral algebraic
groups is finite. Translation identifies its scalar extension with the
finite fibre through the source generic point. -/
theorem finite_kernel_points_of_dominant_sameDim
    {k : Type} [Field k] {X Y : Over (Spec (.of k))} [GrpObj X] [GrpObj Y]
    [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsMonHom f] [IsDominant f.left] [QuasiCompact f.left]
    (hd : topologicalKrullDim X.left = topologicalKrullDim Y.left) :
    Finite (kernelObject f).left := by
  haveI : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have hgen := quasiFiniteAt_generic_of_sameDim X.hom Y.hom f.left (Over.w f) hd
  haveI : IsFinite (f.left.fiberToSpecResidueField (genericPoint Y.left)) :=
    finite_genericFiber f.left hgen
  let x := genericPoint X.left
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
  have hba : a ≫ b = 𝟙 P := by
    apply pullback.hom_ext
    · change (a ≫ b) ≫ p = 𝟙 P ≫ p
      rw [Category.assoc, hb₁, Category.id_comp]
      apply (cancel_mono (kernelInclusion f)).mp
      rw [Category.assoc, hqK, MonObj.comp_mul, GrpObj.comp_inv,
        ← Category.assoc a t', ha₂, ha₁, mul_inv_cancel_right]
    · change (a ≫ b) ≫ t = 𝟙 P ≫ t
      rw [Category.assoc, hb₂, ha₂, Category.id_comp]
  have hba' : a.left ≫ b.left = 𝟙 P.left := congrArg CommaMorphism.left hba
  have hbSurj : Function.Surjective b.left := fun z => ⟨a.left z, by
    rw [← Scheme.Hom.comp_apply, hba']
    rfl⟩
  have hpb : IsPullback q.left t'.left f.left (r ≫ f).left :=
    (Over.forget _).map_isPullback (IsPullback.of_hasPullback f (r ≫ f))
  have hv : (r ≫ f).left (IsLocalRing.closedPoint (X.left.residueField x)) =
      genericPoint Y.left := by
    change f.left (X.left.fromSpecResidueField x (IsLocalRing.closedPoint (X.left.residueField x))) = _
    exact (congrArg f.left (Scheme.fromSpecResidueField_apply x _)).trans
      (genericPoint_map f.left)
  haveI : IsFinite (pullback.snd f.left (r ≫ f).left) :=
    finite_geometricGenericFiber f.left (r ≫ f).left hv
  have hqIso : hpb.isoPullback.hom ≫ pullback.snd _ _ = t'.left :=
    hpb.isoPullback_hom_snd
  haveI : IsFinite t'.left := by rw [← hqIso]; infer_instance
  haveI : Finite T.left := inferInstanceAs (Finite (PrimeSpectrum (X.left.residueField x)))
  haveI : Finite Q.left := by
    apply Set.finite_univ_iff.mp
    rw [← Set.preimage_univ (f := t'.left)]
    exact t'.left.finite_preimage Set.finite_univ
  haveI : Finite P.left := Finite.of_surjective b.left hbSurj
  have ht : IsPullback p.left t.left K.hom T.hom := by
    change IsPullback p.left t.left (toUnit K).left (toUnit T).left
    exact (Over.forget _).map_isPullback (IsPullback.of_hasPullback _ _)
  have t₀ : T.left := IsLocalRing.closedPoint (X.left.residueField x)
  haveI : Surjective T.hom := ⟨fun _ => ⟨t₀, Subsingleton.elim _ _⟩⟩
  haveI : Surjective p.left := MorphismProperty.of_isPullback (P := @Surjective) ht.flip inferInstance
  exact Finite.of_surjective p.left p.left.surjective

/-- A dominant homomorphism of equal-dimensional integral algebraic groups
is locally quasi-finite. -/
theorem locallyQuasiFinite_of_dominant_sameDim
    {k : Type} [Field k] {X Y : Over (Spec (.of k))} [GrpObj X] [GrpObj Y]
    [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsMonHom f] [IsDominant f.left] [QuasiCompact f.left]
    (hd : topologicalKrullDim X.left = topologicalKrullDim Y.left) :
    LocallyQuasiFinite f.left := by
  haveI : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [Over.w]; infer_instance
  haveI : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  haveI := finite_kernel_points_of_dominant_sameDim f hd
  exact ZInQ.FaltingsRestate.locallyQuasiFinite_of_finite_kernel_points f

#print axioms finite_kernel_points_of_dominant_sameDim
#print axioms locallyQuasiFinite_of_dominant_sameDim

end SZRaynaud
