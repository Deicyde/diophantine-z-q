import ZInQKernel.Contrib.OneProof.RC.CMField2.Membership
import ZInQKernel.Contrib.OneProof.RC.X0Branch.Model

/-! Descent on the finite affine chart of the normalization.
Tex 2915–2917, on-the-spot glue (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField TauCeti.ClassFieldTheory
  TauCeti.GlobalNumberFields ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Contrib.CloudW07JacobiansCurves


namespace ZInQ.Manuscript.RC.CMField2
open PreparedParam

attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra

/-- The branch criterion in an embedding in which the proper ideal singular moduli
already descend. The conclusion concerns the regular functions on the normalization. -/
def BranchDescends (N : ℕ) [NeZero N] : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (O : NumberFieldOrder K)
    (hk : Module.finrank ℚ K = 2) (hc : IsTotallyComplex K) (κ : K →+* ℂ)
    (ι : ringClassField O →+* ℂ), ι.comp (algebraMap K (ringClassField O)) = κ →
    (∀ I : O.invertibleProperFractionalIdeals, singularModulus O hk hc κ I ∈ Set.range ι) →
    ∀ d A B C : ℤ, O.discr = d → d < 0 →
      IsCoprime d (N : ℤ) → IsHeegnerForm N d A B C →
      ∀ r, X0Branch.finitePointEval N (cmPoint A B d) r ∈ Set.range ι

theorem affineEval_factor {X : Scheme.{0}} (p : Spec (.of ℂ) ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) (hp : p (default : Spec (.of ℂ)) ∈ U) :
    Spec.map (CommRingCat.ofHom (X0Branch.affineEval p U hp)) ≫ hU.fromSpec = p := by
  have hu : ⊤ ≤ p ⁻¹ᵁ U := fun x _ => by rwa [Subsingleton.elim x (default : Spec (.of ℂ))]
  change Spec.map (p.appLE U ⊤ hu ≫ (Scheme.ΓSpecIso (.of ℂ)).hom) ≫ hU.fromSpec = p
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec p _
    (isAffineOpen_top _) hu, IsAffineOpen.fromSpec_top, ← Scheme.isoSpec_Spec_hom,
    Iso.hom_inv_id_assoc]

/-- A point of an affine open over ℂ descends if all affine evaluations belong
to the embedded field. -/
theorem fieldPoint_of_affineEval_range {X : Scheme.{0}} (q : X ⟶ Spec (.of ℚ))
    (p : FieldPoint q ℂ) {U : X.Opens} (hU : IsAffineOpen U)
    (hp : p.val (default : Spec (.of ℂ)) ∈ U)
    {F : Type} [Field F] [Algebra ℚ F] (ι : F →ₐ[ℚ] ℂ)
    (he : ∀ r, X0Branch.affineEval p.val U hp r ∈ Set.range ι) :
    ∃ x : FieldPoint q F, x.map ι = p := by
  let e := ι.toRingHom
  let ef : F ≃+* e.range := RingEquiv.ofBijective e.rangeRestrict
    ⟨fun _ _ h => e.injective (congrArg Subtype.val h), e.rangeRestrict_surjective⟩
  let a := X0Branch.affineEval p.val U hp
  let aF : Γ(X, U) →+* F := ef.symm.toRingHom.comp (a.codRestrict e.range he)
  have hcomp : e.comp aF = a := by
    ext r
    exact congrArg Subtype.val (ef.apply_symm_apply ⟨a r, he r⟩)
  let x : Spec (.of F) ⟶ X := Spec.map (CommRingCat.ofHom aF) ≫ hU.fromSpec
  have hx : Spec.map (CommRingCat.ofHom e) ≫ x = p.val := by
    dsimp only [x]
    rw [← Category.assoc, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (e.comp aF)) ≫ hU.fromSpec = p.val
    rw [hcomp, affineEval_factor _ hU hp]
  have hxq : x ≫ q = Spec.map (CommRingCat.ofHom (algebraMap ℚ F)) :=
    Spec.homEquiv.injective (CommRingCat.hom_ext (Subsingleton.elim _ _))
  exact ⟨⟨x, hxq⟩, Subtype.ext hx⟩

theorem chart_mem (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    X0Model.complexPoint N τ (default : Spec (.of ℂ)) ∈ X0Branch.finiteChart N := by
  change _ ∈ (X0Model2.jProjection N ⁻¹ᵁ NormalModel.chart 0)
  rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, X0Model2.complexPoint_jProjection]
  change _ ∈ ((NormalModel.chart 0 : NormalModel.P.Opens) : Set NormalModel.P)
  rw [← (NormalModel.isAffineOpen_chart 0).range_fromSpec]
  unfold X0Model2.jLinePoint
  rw [Scheme.Hom.comp_apply]
  exact Set.mem_range_self _

/-- The range condition on the finite j-chart gives descent of the specified branch. -/
theorem fieldPoint_of_finitePointEval_range (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    {F : Type} [Field F] [Algebra ℚ F] (ι : F →ₐ[ℚ] ℂ)
    (he : ∀ r, X0Branch.finitePointEval N τ r ∈ Set.range ι) :
    ∃ x : FieldPoint (X0Branch.model N).overQ F,
      x.map ι = (X0Branch.model N).complexPoint τ := by
  let U := X0Branch.finiteChart N
  have hU : IsAffineOpen U := (NormalModel.isAffineOpen_chart 0).preimage (X0Model2.jProjection N)
  have hp := chart_mem N τ
  exact fieldPoint_of_affineEval_range _ ((X0Branch.model N).complexPoint τ) hU hp ι he

/-- Over a fixed embedded field the chart range condition is also necessary.
It is a test of descent of the specified branch. -/
theorem fieldPoint_iff_finitePointEval_range (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    {F : Type} [Field F] [Algebra ℚ F] (ι : F →ₐ[ℚ] ℂ) :
    (∃ x : FieldPoint (X0Branch.model N).overQ F,
      x.map ι = (X0Branch.model N).complexPoint τ) ↔
    ∀ r, X0Branch.finitePointEval N τ r ∈ Set.range ι := by
  refine ⟨?_, fieldPoint_of_finitePointEval_range N τ ι⟩
  rintro ⟨x, hx⟩ r
  let U := X0Branch.finiteChart N
  let p := X0Model.complexPoint N τ
  let f := Spec.map (CommRingCat.ofHom ι.toRingHom)
  have he : f ≫ x.val = p := congrArg Subtype.val hx
  have mem : p (default : Spec (.of ℂ)) ∈ U := chart_mem N τ
  have hf : ⊤ ≤ (f ≫ x.val) ⁻¹ᵁ U := by
    rw [he]
    exact fun z _ => by rwa [Subsingleton.elim z (default : Spec (.of ℂ))]
  have hu : ⊤ ≤ x.val ⁻¹ᵁ U := by
    intro z _
    rw [Subsingleton.elim z (f (default : Spec (.of ℂ)))]
    change x.val (f (default : Spec (.of ℂ))) ∈ U
    rw [← Scheme.Hom.comp_apply]
    exact hf (show default ∈ (⊤ : (Spec (.of ℂ)).Opens) from trivial)
  have hmap := congrArg (fun g : Γ(X0Model.curve N, U) ⟶ CommRingCat.of ℂ => g r)
    (X0Model.sectionMap_comp x.val ι.toRingHom U hu hf)
  change X0Model.sectionMap (f ≫ x.val) U hf r =
    ι (X0Model.sectionMap x.val U hu r) at hmap
  refine ⟨X0Model.sectionMap x.val U hu r, ?_⟩
  rw [← hmap]
  exact X0Branch.affineEval_congr (U := U) (hf (show default ∈ (⊤ : (Spec (.of ℂ)).Opens)
    from trivial)) mem he |> fun h => DFunLike.congr_fun h r

/-- The field comparison and the branch comparison imply the manuscript's
field-of-definition requirement on the full normalized model. -/
theorem cmFieldOfDefinition_of (N : ℕ) [NeZero N]
    (hm : SingularModulusMemRingClass) (hb : BranchDescends N) :
    CMFieldOfDefinition (X0Branch.model N) := by
  intro K _ _ hk hc O d A B C hdis hd hcop hform
  let κ : K →+* ℂ := Classical.choice inferInstance
  obtain ⟨ι, hι, hj⟩ := hm K O hk hc κ
  exact ⟨ι.toRatAlgHom, fieldPoint_of_finitePointEval_range N _ _
    (hb K O hk hc κ ι hι hj d A B C hdis hd hcop hform)⟩

/-- A valid local coordinate criterion: if the image field contains the two
coordinates and the regular functions lie in the field they generate, then
the chosen point descends. At an open where regular sections have expressions
as rational functions in the plane coordinates with denominators nonzero at
the point, evaluation supplies the displayed containment. -/
theorem fieldPoint_of_eval_mem_adjoin_coordinates (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    {F : Type} [Field F] [Algebra ℚ F] (ι : F →ₐ[ℚ] ℂ)
    (hj : X0Model.analyticJ τ ∈ Set.range ι) (hjn : X0Model.analyticJN N τ ∈ Set.range ι)
    (ha : ∀ r, X0Branch.finitePointEval N τ r ∈ IntermediateField.adjoin ℚ
      {X0Model.analyticJ τ, X0Model.analyticJN N τ}) :
    ∃ x : FieldPoint (X0Branch.model N).overQ F,
      x.map ι = (X0Branch.model N).complexPoint τ := by
  apply fieldPoint_of_finitePointEval_range N τ ι
  have hle : IntermediateField.adjoin ℚ {X0Model.analyticJ τ, X0Model.analyticJN N τ} ≤
      ι.fieldRange := by
    rw [IntermediateField.adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hj, hjn⟩
  exact fun r => hle (ha r)

/-- A local rational expression in the two plane coordinates gives a descent
certificate if its denominator is nonzero at the point. -/
theorem fieldPoint_of_eval_rational_in_coordinates (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    {F : Type} [Field F] [Algebra ℚ F] (ι : F →ₐ[ℚ] ℂ)
    (hj : X0Model.analyticJ τ ∈ Set.range ι) (hjn : X0Model.analyticJN N τ ∈ Set.range ι)
    (hr :
      let e := Polynomial.eval₂RingHom
        (Polynomial.eval₂RingHom (Rat.castHom ℂ) (X0Model.analyticJ τ)) (X0Model.analyticJN N τ)
      ∀ r, ∃ p q : Polynomial (Polynomial ℚ),
        e q ≠ 0 ∧ X0Branch.finitePointEval N τ r * e q = e p) :
    ∃ x : FieldPoint (X0Branch.model N).overQ F,
      x.map ι = (X0Branch.model N).complexPoint τ := by
  let : CharZero F := charZero_of_injective_ringHom (algebraMap ℚ F).injective
  obtain ⟨a, ha⟩ := hj
  obtain ⟨b, hb⟩ := hjn
  let eF := Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Rat.castHom F) a) b
  let eC := Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom (Rat.castHom ℂ) (X0Model.analyticJ τ)) (X0Model.analyticJN N τ)
  have he : ι.toRingHom.comp eF = eC := by
    apply Polynomial.ringHom_ext'
    · rw [RingHom.comp_assoc, Polynomial.eval₂RingHom_comp_C, Polynomial.eval₂RingHom_comp_C]
      apply Polynomial.ringHom_ext'
      · rw [RingHom.comp_assoc, Polynomial.eval₂RingHom_comp_C, Polynomial.eval₂RingHom_comp_C]
        exact Subsingleton.elim _ _
      · simpa [eF, eC] using ha
    · simpa [eF, eC] using hb
  apply fieldPoint_of_finitePointEval_range N τ ι
  intro r
  obtain ⟨p, q, hq, hp⟩ := hr r
  change eC q ≠ 0 at hq
  change X0Branch.finitePointEval N τ r * eC q = eC p at hp
  refine ⟨eF p / eF q, ?_⟩
  rw [map_div₀,
    show ι (eF p) = eC p from DFunLike.congr_fun he p,
    show ι (eF q) = eC q from DFunLike.congr_fun he q]
  exact ((eq_div_iff hq).mpr hp).symm


end ZInQ.Manuscript.RC.CMField2
