import ZInQKernel.Contrib.OneProof.ShimuraSteps
import ZInQKernel.Contrib.OneProof.PicDictionary
import ZInQKernel.Contrib.Dim.FunctionField
import Mathlib.FieldTheory.FinTrdeg

/-!
# Equal dimensions and finiteness of a surjective abelian variety homomorphism

The dimension comparison is at the generic point. Over an algebraic closure of the
source function field, translation injects the geometric kernel into the finite fibre
through the generic point. The geometric-kernel criterion then gives finiteness.
-/

noncomputable section

namespace ShimuraSteps

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace
open PkgI3 PkgI3.AbVar ZInQ.Contrib.Dim ZInQ.Contrib.AbVarBC

section GenericFibre

variable {k : Type} [Field k] {X Y : Scheme.{0}}

private theorem genericPoint_map (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [Surjective f] :
    f (genericPoint X) = genericPoint Y := by
  apply IsGenericPoint.eq _ (genericPoint_spec Y)
  simpa [Set.image_univ, f.surjective.range_eq] using
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

/-- A surjection between equal-dimensional integral schemes of finite type over a field is
quasi-finite at the generic point of the source. -/
private theorem quasiFiniteAt_generic_of_sameDim [IsIntegral X] [IsIntegral Y]
    (a : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType a]
    (b : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType b]
    (f : X ⟶ Y) [Surjective f] [LocallyOfFiniteType f] (hab : f ≫ b = a)
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
    (f : X ⟶ Y) [Surjective f] [LocallyOfFiniteType f] (hq : f.QuasiFiniteAt (genericPoint X)) :
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

/-- Finiteness at the generic point gives a finite generic fibre for a proper surjection. -/
private theorem finite_genericFiber [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [Surjective f] [IsProper f] (hq : f.QuasiFiniteAt (genericPoint X)) :
    IsFinite (f.fiberToSpecResidueField (genericPoint Y)) := by
  have := subsingleton_genericFiber f hq
  let g := f.fiberToSpecResidueField (genericPoint Y)
  have : IsProper g := inferInstanceAs (IsProper (pullback.snd f _))
  have : LocallyQuasiFinite g := LocallyQuasiFinite.of_finite_preimage_singleton g
    (fun _ => Set.toFinite _)
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

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

/-- A finite scheme over a field has finitely many sections over that field. -/
private theorem finite_sections {L : Type} [Field L]
    (g : X ⟶ Spec (CommRingCat.of L)) [IsFinite g] :
    Finite {s : Spec (CommRingCat.of L) ⟶ X // s ≫ g = 𝟙 _} := by
  have : IsAffine X := isAffine_of_isAffineHom g
  let e := X.isoSpec
  let φ := Spec.preimage (e.inv ≫ g)
  have hφ : Spec.map φ = e.inv ≫ g := Spec.map_preimage _
  have hfin : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  let : Algebra L Γ(X, ⊤) := φ.hom.toAlgebra
  have : Module.Finite L Γ(X, ⊤) := hfin
  let mk (s : {s : Spec (CommRingCat.of L) ⟶ X // s ≫ g = 𝟙 _}) :
      Γ(X, ⊤) →ₐ[L] L :=
    { toRingHom := (Spec.preimage (s.1 ≫ e.hom)).hom
      commutes' := fun l => by
        have h : φ ≫ Spec.preimage (s.1 ≫ e.hom) = 𝟙 _ := by
          apply Spec.map_injective
          rw [Spec.map_comp, hφ, Spec.map_preimage, Category.assoc,
            e.hom_inv_id_assoc, s.2, Spec.map_id]
        exact congrArg (fun r : CommRingCat.of L ⟶ CommRingCat.of L => r.hom l) h }
  apply Finite.of_injective mk
  intro s t h
  apply Subtype.ext
  have e' : Spec.preimage (s.1 ≫ e.hom) = Spec.preimage (t.1 ≫ e.hom) := by
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom h
  have hh := congrArg Spec.map e'
  simp only [Spec.map_preimage] at hh
  exact (cancel_mono e.hom).mp hh

end GenericFibre

/-- The finite fibre through the generic point bounds the number of geometric kernel points. -/
private theorem finite_kerPts_of_sameDim {k : Type} [Field k] {A B : AbVar k}
    (f : Hom A B) [Surjective f.hom.left] (hd : A.dim = B.dim) :
    {p : A.Pt (AlgebraicClosure k) | p ≫ f.hom = 1}.Finite := by
  have : IsIntegral A.X.left := GeometricallyIntegral.isIntegral_of_subsingleton A.X.hom
  have : IsIntegral B.X.left := GeometricallyIntegral.isIntegral_of_subsingleton B.X.hom
  have : IsProper f.hom.left := MulRigidity.isProper_left A B f.hom
  have hq := quasiFiniteAt_generic_of_sameDim A.X.hom B.X.hom f.hom.left (Over.w f.hom) hd
  have := finite_genericFiber f.hom.left hq
  let F := A.X.left.functionField
  let : Algebra k F := functionFieldAlgebra k A.X.left A.X.hom
  let q : A.Pt F := Over.homMk (A.X.left.fromSpecStalk (genericPoint A.X.left))
    (fromSpecStalk_generic_comp A.X.hom)
  let L := AlgebraicClosure F
  let i : F →ₐ[k] L := IsScalarTower.toAlgHom k F L
  let p : A.Pt L := extPt A i q
  let b : B.Pt L := p ≫ f.hom
  let v : Spec (CommRingCat.of L) ⟶ B.X.left := b.left
  have hv : v (IsLocalRing.closedPoint (CommRingCat.of L)) = genericPoint B.X.left := by
    change f.hom.left (A.X.left.fromSpecStalk (genericPoint A.X.left)
      (Spec.map (CommRingCat.ofHom i.toRingHom) (IsLocalRing.closedPoint (CommRingCat.of L)))) = _
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint, genericPoint_map f.hom.left]
  let g := pullback.snd f.hom.left v
  have : IsFinite g := finite_geometricGenericFiber f.hom.left v hv
  have := finite_sections g
  let κ : AlgebraicClosure k →ₐ[k] L := IsAlgClosed.lift
  let translate (s : A.Pt (AlgebraicClosure k)) : A.Pt L := extPt A κ s * p
  have hcomp (s : {s : A.Pt (AlgebraicClosure k) // s ≫ f.hom = 1}) :
      translate s.1 ≫ f.hom = b := by
    change (extPt A κ s.1 * p) ≫ f.hom = b
    rw [MonObj.mul_comp, extPt_apply, Category.assoc, s.2, MonObj.comp_one, _root_.one_mul]
  let lift (s : {s : A.Pt (AlgebraicClosure k) // s ≫ f.hom = 1}) :
      {t : Spec (CommRingCat.of L) ⟶ pullback f.hom.left v // t ≫ g = 𝟙 _} :=
    ⟨pullback.lift (f := f.hom.left) (g := v) (translate s.1).left (𝟙 _) (by
      rw [Category.id_comp]
      exact congrArg (·.left) (hcomp s)),
      pullback.lift_snd _ _ _⟩
  change Finite {s : A.Pt (AlgebraicClosure k) // s ≫ f.hom = 1}
  apply Finite.of_injective lift
  intro s t h
  have hfst (s : {s : A.Pt (AlgebraicClosure k) // s ≫ f.hom = 1}) :
      (lift s).1 ≫ pullback.fst f.hom.left v = (translate s.1).left :=
    pullback.lift_fst _ _ _
  have h' : (translate s.1).left = (translate t.1).left := by
    rw [← hfst s, ← hfst t, h]
  exact Subtype.ext (extPt_injective A κ (mul_right_cancel
    (show translate s.1 = translate t.1 from Over.OverMorphism.ext h')))

/-- A surjective homomorphism of equal-dimensional abelian varieties over `ℚ` is finite. -/
theorem sameDimSurjectiveFinite : SameDimSurjectiveFinite := by
  intro A B f hd hf
  exact PicDict.finiteOfFiniteKerPts ℚ A B f (finite_kerPts_of_sameDim f hd)

/-- Shimura's existing quotient row follows from the printed form and the Hecke bridge. -/
theorem shimuraThm1Af_of_printed' :
    ShimuraThm1AsPrinted → ShimuraHeckeRelations → R16Thm1b.ShimuraThm1Af :=
  fun hp hh => shimuraThm1Af_of_printed hp hh sameDimSurjectiveFinite

end ShimuraSteps
