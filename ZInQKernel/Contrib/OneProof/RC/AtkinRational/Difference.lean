import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Based
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Infinity
import ZInQKernel.Contrib.OneProof.RC.AtkinRational.Reduction

/-! Represent the signed difference along the modular curve itself. There
is no need to construct a product of projective Weierstrass schemes.
Tex 2943–2946 and 8487–8489; on the spot (c), by extending the generic
difference and checking its reading in each valuation stalk. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section

open scoped Classical MatrixGroups TauCeti.ExactDivisor
open AlgebraicGeometry CategoryTheory Limits UpperHalfPlane WeierstrassCurve ModularCurve IsLocalRing
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Contrib.RC53Assist.AbelianCurve ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.AtkinPin ZInQ.Manuscript.RC.ParamAtScale

namespace ZInQ.Manuscript.RC.AtkinRational

/-- Extend the generic difference by properness. At each point, the local
ring of the modular curve is a valuation ring containing ℚ. Its good
reduction homomorphism reads the extended difference on the residue
field, and scalar extension gives the formula on the original field. -/
theorem representsDifference_of_origin {N : ℕ} [NeZero N]
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (o : Spec (.of ℚ) ⟶ Proj E.toProjective.grading) (ho : projectiveValue o = 0) :
    RepresentsDifference N E := by
  let X := (X0Branch.model N).X
  let p := (X0Branch.model N).overQ
  let Y := Proj E.toProjective.grading
  let q := projectiveOverQ E
  let : IsIntegral X := (X0Branch.model N).integral
  let : Smooth p := (X0Branch.model N).smooth
  let : X.Over (Spec (.of ℚ)) := ⟨p⟩
  let : Y.Over (Spec (.of ℚ)) := ⟨q⟩
  have : IsProper (Y ↘ Spec (.of ℚ)) := projectiveOverQ_proper E
  have : Y.IsSeparated :=
    ⟨by rw [← terminal.comp_from (Y ↘ Spec (.of ℚ))]; infer_instance⟩
  let valRing (y : X) : ValuationRing (X.presheaf.stalk y) :=
    smooth_curve_valuation_stalk p (model_dimension (X0Branch.model N)) y
  let K := X.functionField
  let : Algebra ℚ K := (p.structureStalk (genericPoint X)).hom.toAlgebra
  let η := X.fromSpecFunctionField
  intro u w _ _ e
  let A := projectiveValue (η ≫ u) - e • projectiveValue (η ≫ w)
  obtain ⟨g, hg⟩ := projectiveValue_surjective_of_origin E o ho A
  obtain ⟨D, hD, hgen⟩ := Scheme.exists_hom_of_valuationRing_stalk
    (base := Spec (.of ℚ)) valRing g (spec_to_rat _ _)
  refine ⟨D, hD.1, ?_⟩
  intro F _ _ x
  let xf := Scheme.SpecToEquivOfField F X x.val
  let y := xf.1
  let B := X.presheaf.stalk y
  let : ValuationRing B := valRing y
  let v := ValuationRing.valuation B K
  let R := v.valuationSubring
  let ρ : B ≃+* R := ValuationRing.equivInteger B K
  let : Algebra ℚ R := (ρ.toRingHom.comp (p.structureStalk y).hom).toAlgebra
  let : IsScalarTower ℚ R K := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let l := Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ X.fromSpecStalk y
  let s := Spec.map (CommRingCat.ofHom (residue R))
  have hη : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l = η := by
    unfold l
    rw [← Category.assoc, ← Spec.map_comp]
    have hρ : (algebraMap R K).comp ρ.toRingHom = algebraMap B K := by
      ext z
      rfl
    change Spec.map (CommRingCat.ofHom ((algebraMap R K).comp ρ.toRingHom)) ≫ _ = _
    rw [hρ]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes y)
  let : IsLocalHom xf.2.hom := ⟨fun z hz => isUnit_iff_ne_zero.mpr fun h =>
    hz.ne_zero (by rw [h, map_zero])⟩
  let : IsLocalHom (residue B) := ⟨fun z hz => by
    by_contra h
    exact hz.ne_zero (Ideal.Quotient.eq_zero_iff_mem.2 h)⟩
  let : IsLocalHom ρ.symm.toRingHom := ⟨fun z hz => by
    simpa only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply]
      using hz.map ρ.toRingHom⟩
  let : IsLocalHom (xf.2.hom.comp (residue B)) := RingHom.isLocalHom_comp _ _
  let b : R →+* F := (xf.2.hom.comp (residue B)).comp ρ.symm.toRingHom
  have : IsLocalHom b := RingHom.isLocalHom_comp _ _
  let j : ResidueField R →ₐ[ℚ] F :=
    { __ := ResidueField.lift b
      commutes' := DFunLike.congr_fun (RingHom.ext_rat
        ((ResidueField.lift b).comp (algebraMap ℚ (ResidueField R))) (algebraMap ℚ F)) }
  have hx : Spec.map (CommRingCat.ofHom j.toRingHom) ≫ s ≫ l = x.val := by
    unfold s l
    simp only [← Category.assoc, ← Spec.map_comp]
    have hcomp : CommRingCat.ofHom ρ.toRingHom ≫ CommRingCat.ofHom (residue R) ≫
        CommRingCat.ofHom j.toRingHom = X.residue y ≫ xf.2 := by
      apply CommRingCat.hom_ext
      ext z
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
      change ResidueField.lift b (residue R (ρ z)) = xf.2.hom (residue B z)
      rw [ResidueField.lift_residue_apply]
      change xf.2.hom (residue B (ρ.symm (ρ z))) = _
      rw [ρ.symm_apply_apply]
    change Spec.map (CommRingCat.ofHom ρ.toRingHom ≫
      CommRingCat.ofHom (residue R) ≫ CommRingCat.ofHom j.toRingHom) ≫ _ = _
    rw [hcomp]
    change Spec.map (X.residue y ≫ xf.2) ≫ X.fromSpecStalk y = _
    rw [Spec.map_comp, Category.assoc]
    exact (Scheme.SpecToEquivOfField F X).left_inv x.val
  have hr (t : X ⟶ Y) :
      projectiveValue (x.val ≫ t) =
        Affine.Point.map (W' := E.toAffine) j (projectiveReduction v E (projectiveValue (η ≫ t))) := by
    rw [← hx]
    simp only [Category.assoc]
    rw [← projectiveValue_map, projectiveValue_specialization v E o ho (l ≫ t),
      ← Category.assoc, hη]
  rw [hr D, hr u, hr w, hgen, hg]
  simp only [A, map_sub, map_zsmul]

/-- The pinned chart formula gives the based identity for the normalized
parametrization on the rational curve, with the constructed involution. -/
theorem basedAtkinAtScale {N Q : ℕ} [NeZero N] {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (f : HeckeRing.GL2.Newform N 2) (hχ : f.χ = 1) (hQ : Q ∥ N)
    (Lat : PeriodPair) (κ : ℂ) (hLat : IsLatticeOf E Lat)
    (π : (X0Branch.model N).X ⟶ Proj E.toProjective.grading)
    (hπ : π ≫ projectiveOverQ E = (X0Branch.model N).overQ)
    (hscale : ∀ τ : ℍ, projectiveValue (((X0Branch.model N).complexPoint τ).comp π hπ).val =
      phiAn E (f.toCuspFormGamma0 hχ) Lat κ τ)
    (hzero : projectiveValue ((infinityPoint N).comp π hπ).val = 0) :
    BasedAtkinOnPoints (X0Branch.model N) (rationalAtkin hQ) π hπ (infinityPoint N)
      (signUnit f hχ hQ : ℤ) := by
  let X := X0Branch.model N
  let W := rationalAtkin hQ
  let e := (signUnit f hχ hQ : ℤ)
  obtain ⟨D, hD, hread⟩ := representsDifference_of_origin E ((infinityPoint N).comp π hπ).val hzero
    (W.hom ≫ π) π (by rw [Category.assoc, hπ, W.overQ]) hπ e
  exact based_of_representedDifference W π hπ (infinityPoint N) hzero e
    (projectiveValue_transform_chart X f hχ hQ Lat κ hLat π hπ hscale) D hD
    (fun F _ _ x => by simpa only [FieldPoint.comp, Category.assoc] using hread F x)

/-- The generic fibre of (O.7) at the fixed scale, with both the rational
involution and the based field identity constructed at the pinned sign.
The rational representative of the manuscript's scale remains an input. -/
theorem genericFibreAtScale {ℓ Q : ℕ} [(Ecurve ℓ).IsElliptic]
    [NeZero (newformLevel (Ecurve ℓ))]
    (f : HeckeRing.GL2.Newform (newformLevel (Ecurve ℓ)) 2) (hχ : f.χ = 1)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 (f.toCuspFormGamma0 hχ)).coeff n =
      ((Ecurve ℓ).LFunction n : ℂ))
    (hQ : Q ∥ newformLevel (Ecurve ℓ)) {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat)
    {κ : ℂ} (hκ : IsParamScale (newformLevel (Ecurve ℓ)) (f.toCuspFormGamma0 hχ) Lat κ)
    (hr : ∃ c : ℚ, (c : ℂ) = κ) :
    let N := newformLevel (Ecurve ℓ)
    let X := X0Branch.model N
    let W := rationalAtkin hQ
    let e := (signUnit f hχ hQ : ℤ)
    ∃ (π : X.X ⟶ Proj (Ecurve ℓ).toProjective.grading)
      (hπ : π ≫ projectiveOverQ (Ecurve ℓ) = X.overQ), IsDominant π ∧
      (∀ τ : ℍ, projectiveValue ((X.complexPoint τ).comp π hπ).val =
        phiAn (Ecurve ℓ) (f.toCuspFormGamma0 hχ) Lat κ τ) ∧
      projectiveValue ((infinityPoint N).comp π hπ).val = 0 ∧
      BasedAtkinOnPoints X W π hπ (infinityPoint N) e ∧
      ∀ (F : Type) [Field F] [Algebra ℚ F] (x : FieldPoint X.overQ F),
        projectiveValue ((x.comp W.hom W.overQ).comp π hπ).val =
          e • projectiveValue (x.comp π hπ).val +
            Affine.Point.map (W' := (Ecurve ℓ).toAffine) (Algebra.ofId ℚ F)
              (projectiveValue (((infinityPoint N).comp W.hom W.overQ).comp π hπ).val) := by
  obtain ⟨π, hπ, hd, hscale, hzero⟩ :=
    algebraicParametrizationAtScale_atInfinity (f.toCuspFormGamma0 hχ) hf hLat hκ hr
  have h := basedAtkinAtScale f hχ hQ Lat κ hLat π hπ hscale hzero
  exact ⟨π, hπ, hd, hscale, hzero, h,
    translatedAtkinAtInfinity (rationalAtkin hQ) π hπ _ h hzero⟩


end ZInQ.Manuscript.RC.AtkinRational
