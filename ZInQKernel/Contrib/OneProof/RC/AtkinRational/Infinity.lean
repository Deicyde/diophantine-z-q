import ZInQKernel.Contrib.OneProof.RC.AtkinPin.Generic

/-! The actual parametrization sends the rational formal cusp to zero.
Tex 1785–1787 and 2943–2946: pole comparison, on the spot (c). -/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory UpperHalfPlane WeierstrassCurve ModularCurve
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Contrib.RC53Assist.IsogenyScheme
open ZInQ.Manuscript.RC.PreparedParam ZInQ.Manuscript.RC.AtkinPin
open ZInQ.Manuscript.RC.ModFnField ZInQ.Manuscript.RC.ParamAtScale

namespace ZInQ.Manuscript.RC.AtkinRational

set_option backward.isDefEq.respectTransparency.types false in
private theorem formalClosedPoint :
    Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := ℚ)))
      (default : Spec (.of ℚ)) = IsLocalRing.closedPoint (PowerSeries ℚ) := by
  apply PrimeSpectrum.ext
  rw [Spec.map_apply]
  rw [show (default : Spec (.of ℚ)) = (⊥ : PrimeSpectrum ℚ) from Subsingleton.elim _ _]
  change Ideal.comap (PowerSeries.constantCoeff (R := ℚ))
    ((⊥ : PrimeSpectrum ℚ).asIdeal) = IsLocalRing.maximalIdeal (PowerSeries ℚ)
  rw [PrimeSpectrum.asIdeal_bot]
  exact PowerSeries.ker_coeff_eq_max_ideal

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A pole of the pulled back affine coordinate forces the image of the
formal cusp off the affine chart, where the point reading is zero. -/
theorem infinity_zero_of_pole {N : ℕ} [NeZero N] {E : WeierstrassCurve ℚ} [E.IsElliptic]
    (π : (X0Branch.model N).X ⟶ Proj E.toProjective.grading)
    (hπ : π ≫ projectiveOverQ E = (X0Branch.model N).overQ)
    (ι : E.toAffine.FunctionField →+* modularFunctionField N)
    (hgen : (X0Model.curve N).fromSpecFunctionField ≫ π =
      Spec.map (CommRingCat.ofHom ((X0Model.functionField N).symm.toRingHom.comp
        (ι.comp (projFunctionFieldEquiv E).toRingHom))) ≫
          (Proj E.toProjective.grading).fromSpecFunctionField)
    (hpole : ((ι E.toAffine.genericX : modularFunctionField N) : LaurentSeries ℚ).coeff (-2) ≠ 0) :
    projectiveValue ((infinityPoint N).comp π hπ).val = 0 := by
  classical
  let : IsIntegral (X0Branch.model N).X := (X0Branch.model N).integral
  let Y := Proj E.toProjective.grading
  let V := Proj.basicOpen E.toProjective.grading (E.toProjective.coord 2)
  let U := π ⁻¹ᵁ V
  let u := X0Model.formalQArc N
  change projectiveValue (X0Model.cusp N ≫ π) = 0
  have hc : (X0Model.cusp N ≫ π) default = pointO E := by
    by_contra h
    have hm := coord_zero_mem_of_coord_two_mem E ((X0Model.cusp N ≫ π) default)
    have hv : (X0Model.cusp N ≫ π) default ∈ V := by
      apply (Proj.mem_basicOpen _ _ _).2
      intro hz
      exact h (eq_pointO_of_coord_mem E _ (hm hz) hz)
    have hu : ⊤ ≤ u ⁻¹ᵁ U := by
      apply (Scheme.preimage_eq_top_of_closedPoint_mem _ _).ge
      change (X0Model.formalQArc N ≫ π) (IsLocalRing.closedPoint (PowerSeries ℚ)) ∈ V
      rw [← formalClosedPoint, ← Scheme.Hom.comp_apply, ← Category.assoc]
      exact hv
    let : Nonempty U := ⟨⟨u (IsLocalRing.closedPoint (PowerSeries ℚ)), hu trivial⟩⟩
    let r := π.app V (sectionXOverZ E)
    let A := algebraMap (PowerSeries ℚ) (LaurentSeries ℚ)
    have ha : ⊤ ≤ (Spec.map (CommRingCat.ofHom A) ≫ u) ⁻¹ᵁ U := fun x _ =>
      hu (show Spec.map (CommRingCat.ofHom A) x ∈ ⊤ from trivial)
    have hb : ⊤ ≤ (X0Model.genericMap N (modularFunctionField N).subtype) ⁻¹ᵁ U := by
      rwa [X0Model.formalQArc_generic] at ha
    have he : A (X0Model.sectionMap u U hu r) =
        (ι E.toAffine.genericX : LaurentSeries ℚ) := by
      calc
        _ = X0Model.sectionMap (Spec.map (CommRingCat.ofHom A) ≫ u) U ha r :=
          (congrArg (fun k => k r) (X0Model.sectionMap_comp u A U hu ha)).symm
        _ = X0Model.sectionMap (X0Model.genericMap N (modularFunctionField N).subtype) U hb r := by
          simp only [u, A, X0Model.formalQArc_generic]
        _ = _ := by
          rw [X0Model.sectionMap_generic, CommRingCat.comp_apply]
          have hgen' := germToFunctionField_pullback π _ hgen V (sectionXOverZ E)
          change (X0Model.curve N).germToFunctionField U r = _ at hgen'
          rw [hgen']
          change ((X0Model.functionField N)
            ((X0Model.functionField N).symm (ι (projFunctionFieldEquiv E
              (Y.germToFunctionField V (sectionXOverZ E))))) : LaurentSeries ℚ) = _
          rw [RingEquiv.apply_symm_apply, projFunctionFieldEquiv_sectionXOverZ]
    apply hpole
    rw [← he]
    exact ModularCurve.ofPowerSeries_coeff_of_neg _ (by norm_num)
  simp only [projectiveValue, hc, dite_true]

set_option backward.isDefEq.respectTransparency false in
/-- The fixed scale is an input. Construct the same at-scale morphism with
its generic coordinates retained long enough to identify the formal cusp. -/
theorem algebraicParametrizationAtScale_atInfinity {ℓ : ℕ} [(Ecurve ℓ).IsElliptic]
    [NeZero (newformLevel (Ecurve ℓ))]
    (f : CuspForm (CongruenceSubgroup.Gamma0 (newformLevel (Ecurve ℓ)) :
      Subgroup (GL (Fin 2) ℝ)) 2)
    (hf : ∀ n : ℕ, 0 < n → (qExpansion 1 f).coeff n = (Ecurve ℓ).LFunction n)
    {Lat : PeriodPair} (hLat : IsLatticeOf (Ecurve ℓ) Lat) {κ : ℂ}
    (hκ : IsParamScale (newformLevel (Ecurve ℓ)) f Lat κ) (hr : ∃ c : ℚ, (c : ℂ) = κ) :
    let N := newformLevel (Ecurve ℓ)
    let X := X0Branch.model N
    ∃ (π : X.X ⟶ Proj (Ecurve ℓ).toProjective.grading)
      (hπ : π ≫ projectiveOverQ (Ecurve ℓ) = X.overQ), IsDominant π ∧
      (∀ τ : ℍ, projectiveValue ((X.complexPoint τ).comp π hπ).val =
        phiAn (Ecurve ℓ) f Lat κ τ) ∧
      projectiveValue ((infinityPoint N).comp π hπ).val = 0 := by
  obtain ⟨c, rfl⟩ := hr
  have hc : c ≠ 0 := fun h => hκ.1 (by simp [h])
  let E := Ecurve ℓ
  let N := newformLevel E
  let X := X0Branch.model N
  let H := ModFnClassify.complexCuspClassification N
  obtain ⟨ι, π, hπ, hd, hg, hx, hy⟩ :=
    dominant_morphism_of_classification E X H f hf hLat hκ
  obtain ⟨a, b, ha, ha', _, _⟩ :=
    coordinates_in_modularFunctionField_with_equation E H f hf hLat hκ
  have he := Realizes.eq_of_eventuallyEq hx ha' (Filter.Eventually.of_forall fun _ => rfl)
  have hlead := congrArg (fun s : LaurentSeries ℂ => s.coeff (-2)) he
  simp only [complexify_coeff] at hlead
  have hpole : (ι E.toAffine.genericX : LaurentSeries ℚ).coeff (-2) ≠ 0 := by
    intro h
    rw [h, Rat.cast_zero, ha] at hlead
    exact (pow_ne_zero _ (inv_ne_zero hκ.1)) hlead.symm
  exact ⟨π, hπ, hd, ModFnClassify.projective_value_of_expansions
    E X f hf hLat hc π hπ ι hg hx hy, infinity_zero_of_pole π hπ ι hg hpole⟩


end ZInQ.Manuscript.RC.AtkinRational
