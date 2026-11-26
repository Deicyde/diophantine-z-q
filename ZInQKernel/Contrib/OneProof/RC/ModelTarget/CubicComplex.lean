import ZInQKernel.Contrib.OneProof.RC.ModelTarget.Read
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectivePoints

/-! The complex reading of the good cubic, tex 8476–8479: the complex points of its generic
fibre, with the group law induced from the cubic, read through the generic identification
`cubicJE` by the coordinate value `projectiveValue` of `J0Cusps`. The reading is a
monoid homomorphism because the cubic's multiplication computes Mathlib's group law at
every field point. On the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open WeierstrassCurve WeierstrassCurve.ModelTorsion
open scoped WeierstrassCurve CategoryTheory.Obj WeierstrassCurve.Projective

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace ZInQ.Manuscript.RC.ModelTarget

open GoodReduction (generic)
open PMWire (complexBase ellipticTarget)

/-- On the fixed rational cubic, `J0Cusps`'s coordinate value is the field value. -/
theorem projectiveValue_eq_fieldValue (E : WeierstrassCurve ℚ) [E.IsElliptic] {F : Type} [Field F]
    [Algebra ℚ F] (p : Spec (.of F) ⟶ Proj E.toProjective.grading)
    (hp : p ≫ projStructure E = Spec.map (CommRingCat.ofHom (algebraMap ℚ F))) :
    PreparedParam.projectiveValue p = fieldValue E (algebraMap ℚ F) p hp := by
  obtain ⟨v, hv, i, hi, rfl⟩ := exists_chartMorphism E (algebraMap ℚ F) p hp
  rw [fieldValue_chartMorphism]
  have hns := nonsingular_of_unit_coord E (algebraMap ℚ F) v hv i hi.ne_zero
  exact J0Cusps.projectiveValue_chartMorphism E v hns i hi

theorem fieldValue_eqToHom {S F : Type} [CommRing S] [Field F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve S} (h : W₁ = W₂) (g : S →+* F)
    (q : Spec (.of F) ⟶ Proj W₁.toProjective.grading)
    (hq : q ≫ projStructure W₁ = Spec.map (CommRingCat.ofHom g))
    (hq' : (q ≫ (eqToHom (congrArg cubic h)).left) ≫ projStructure W₂ = Spec.map (CommRingCat.ofHom g)) :
    fieldValue W₂ g (q ≫ (eqToHom (congrArg cubic h)).left) hq' =
      pointCongr (congrArg (fun W => W.map g) h) (fieldValue W₁ g q hq) := by
  subst h
  simp only [eqToHom_refl, Over.id_left, Category.comp_id]
  rfl

variable {ell : ℕ} [Fact ell.Prime] {W₀ : WeierstrassCurve ℤ}

/-- The ring map from the detector ring to `ℂ` through `ℚ`. -/
abbrev complexRing (ell : ℕ) [Fact ell.Prime] : LocalIntegers ell →+* ℂ :=
  (algebraMap ℚ ℂ).comp (algebraMap (LocalIntegers ell) ℚ)

theorem complex_structure :
    complexBase.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (LocalIntegers ell) ℚ)) =
      Spec.map (CommRingCat.ofHom (complexRing ell)) := by
  change Spec.map _ ≫ _ = _
  rw [← Spec.map_comp, CommRingCat.ofHom_comp]

/-- The comparison of the complex point object with the field point over the detector ring. -/
def complexIso (ell : ℕ) [Fact ell.Prime] : fieldPt (complexRing ell) ≅
    Over.mk (complexBase.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap (LocalIntegers ell) ℚ))) :=
  Over.isoMk (Iso.refl _) (by simp [complex_structure])

/-- A complex point of the generic fibre, read as a point of the cubic over `R → ℂ`. -/
def complexUp (a : complexBase ⟶ (generic (LocalIntegers ell) ℚ).obj (detE ell W₀)) :
    fieldPt (complexRing ell) ⟶ cubic (detW ell W₀) :=
  (complexIso ell).hom ≫ (upHom _ (detE ell W₀) a : _ ⟶ cubic (detW ell W₀))

theorem complexUp_left (a : complexBase ⟶ (generic (LocalIntegers ell) ℚ).obj (detE ell W₀)) :
    (complexUp a).left = a.left ≫ pullback.fst _ _ := by
  change 𝟙 _ ≫ (a.left ≫ pullback.fst _ _) = _
  rw [Category.id_comp]

theorem complex_curve (ell : ℕ) [Fact ell.Prime] (W₀ : WeierstrassCurve ℤ) :
    (detW ell W₀).map (complexRing ell) = (W₀⁄ℚ)⁄ℂ := by
  rw [detW_map_eq (complexRing ell) ((algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ))]
  exact (WeierstrassCurve.map_map W₀ _ _).symm

omit [Fact ell.Prime] in
/-- The value of a field point through `bcIso` followed by an identification of curves. -/
theorem bcEq_value {R S F : Type} [CommRing R] [CommRing S] [Field F] [DecidableEq F]
    (W : WeierstrassCurve R) (ψ : R →+* S) (W' : WeierstrassCurve S) (h : W.map ψ = W')
    [W.IsElliptic] [(W.map ψ).IsElliptic] [IsReduced (baseChangeScheme W ψ)]
    [IsReduced (Proj (W.map ψ).toProjective.grading)]
    (g : S →+* F) (p : Spec (.of F) ⟶ baseChangeScheme W ψ)
    (hp : p ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom g))
    (hp' : (p ≫ (bcIso W ψ ≪≫ eqToIso (congrArg cubic h)).hom.left) ≫ projStructure W' =
      Spec.map (CommRingCat.ofHom g)) :
    fieldValue W' g (p ≫ (bcIso W ψ ≪≫ eqToIso (congrArg cubic h)).hom.left) hp' =
      Projective.Point.toAffine (W'.toProjective.map g) (bcVec W ψ g p hp) := by
  subst h
  have e : p ≫ (bcIso W ψ ≪≫ eqToIso (congrArg cubic (rfl : W.map ψ = W.map ψ))).hom.left =
      p ≫ (bcHom W ψ).left := by
    simp [bcIso]
  rw [fieldValue_congr (W.map ψ) g e _ (comp_structure _
    (exists_baseChangeHom W ψ).choose_spec.choose hp)]
  exact bcHom_value W ψ g p hp

theorem detRational_isElliptic (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) : (W₀⁄ℚ).IsElliptic := by
  have := ModelNeron.isElliptic_at_detector ell W₀ hΔ
  rw [show W₀⁄ℚ = (detW ell W₀).map (algebraMap (LocalIntegers ell) ℚ) from
    (detW_map_eq (algebraMap (LocalIntegers ell) ℚ) (algebraMap ℤ ℚ)).symm]
  infer_instance

/-- The generic identification of the good cubic, written as `bcIso` followed by the
equality of curves `W₀.map (ℤ → R) .map (R → ℚ) = W₀⁄ℚ`; the same composite as
`detGenericIso`, unfolded. -/
def cubicJE (h₅ : 5 ≤ ell) (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) :
    (generic (LocalIntegers ell) ℚ).obj (detE ell W₀) ≅ ellipticTarget (W₀⁄ℚ) :=
  haveI := ModelNeron.isElliptic_at_detector ell W₀ hΔ
  haveI := reduced_mapped (algebraMap (LocalIntegers ell) ℚ) h₅ hΔ
  haveI := reduced_baseChange (algebraMap (LocalIntegers ell) ℚ) h₅ hΔ
  bcIso (detW ell W₀) (algebraMap (LocalIntegers ell) ℚ) ≪≫
    eqToIso (congrArg cubic (detW_map_eq (algebraMap (LocalIntegers ell) ℚ) (algebraMap ℤ ℚ)))

/-- The complex value of a generic point of the good cubic read through `cubicJE` is
the value of its image in the cubic, carried to the fixed rational equation. -/
theorem projectiveValue_cubicJE (h₅ : 5 ≤ ell) (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ)
    (a : complexBase ⟶ (generic (LocalIntegers ell) ℚ).obj (detE ell W₀)) :
    haveI : (W₀⁄ℚ).IsElliptic := detRational_isElliptic hΔ
    PreparedParam.projectiveValue (a.left ≫ (cubicJE h₅ hΔ).hom.left) =
      pointCongr (complex_curve ell W₀) (val (detW ell W₀) (complexUp a)) := by
  haveI : (W₀⁄ℚ).IsElliptic := detRational_isElliptic hΔ
  haveI := ModelNeron.isElliptic_at_detector ell W₀ hΔ
  haveI := reduced_mapped (algebraMap (LocalIntegers ell) ℚ) h₅ hΔ
  haveI := reduced_baseChange (algebraMap (LocalIntegers ell) ℚ) h₅ hΔ
  let ψ := algebraMap (LocalIntegers ell) ℚ
  let h := detW_map_eq (W₀ := W₀) ψ (algebraMap ℤ ℚ)
  have ha : a.left ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)) := Over.w a
  have hp2 : (a.left ≫ (cubicJE h₅ hΔ).hom.left) ≫ projStructure (W₀⁄ℚ) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)) :=
    J0Cusps.schemeMapsToRat_unique _ _
  have e1 : fieldValue (W₀⁄ℚ) (algebraMap ℚ ℂ) (a.left ≫ (cubicJE h₅ hΔ).hom.left) hp2 =
      Projective.Point.toAffine ((W₀⁄ℚ).toProjective.map (algebraMap ℚ ℂ))
        (bcVec (detW ell W₀) ψ (algebraMap ℚ ℂ) a.left ha) := by
    unfold cubicJE
    exact bcEq_value (detW ell W₀) ψ (W₀⁄ℚ) h (algebraMap ℚ ℂ) a.left ha hp2
  have e2 : val (detW ell W₀) (complexUp a) =
      Projective.Point.toAffine ((detW ell W₀).toProjective.map (complexRing ell))
        (bcVec (detW ell W₀) ψ (algebraMap ℚ ℂ) a.left ha) := by
    unfold val
    exact (fieldValue_congr (detW ell W₀) _ (complexUp_left a) _
      (fst_structure (detW ell W₀) ψ (algebraMap ℚ ℂ) a.left ha)).trans
      (fieldValue_eq_bcVec (detW ell W₀) ψ (algebraMap ℚ ℂ) a.left ha)
  rw [projectiveValue_eq_fieldValue (W₀⁄ℚ) _ hp2, e1, e2, pointCongr_toAffine]
  rfl

/-- **The complex reading of the good cubic** (`readComplex` of `PMWire.GoodRow`). -/
def readComplexCubic (h₅ : 5 ≤ ell) (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ) :
    letI := weierstrassModelGrp ell h₅ W₀ hΔ
    (complexBase ⟶ (generic (LocalIntegers ell) ℚ).obj (detE ell W₀)) →*
      Multiplicative ((W₀⁄ℚ).baseChange ℂ).toAffine.Point :=
  letI := weierstrassModelGrp ell h₅ W₀ hΔ
  haveI : (W₀⁄ℚ).IsElliptic := detRational_isElliptic hΔ
  MonoidHom.mk' (fun a => Multiplicative.ofAdd
      (PreparedParam.projectiveValue (a.left ≫ (cubicJE h₅ hΔ).hom.left))) (fun a b => by
    haveI := ModelNeron.isElliptic_at_detector ell W₀ hΔ
    haveI : IsReduced (cubic (detW ell W₀) ⊗ cubic (detW ell W₀)).left :=
      isReduced_of_smooth_hom (ZInQ.Contrib.NeronC.smooth_tensor _ _
        (weierstrassModel_smooth ell h₅ W₀ hΔ) (weierstrassModel_smooth ell h₅ W₀ hΔ))
    have e : complexUp (a * b) = lift (complexUp a) (complexUp b) ≫ cubicMul (detW ell W₀) := by
      apply Over.OverMorphism.ext
      rw [complexUp_left, mul_left_fst]
      simp only [complexUp, Over.comp_left, comp_lift]
      simp [complexIso]
      rfl
    show Multiplicative.ofAdd _ = Multiplicative.ofAdd _ * Multiplicative.ofAdd _
    rw [projectiveValue_cubicJE h₅ hΔ (a * b), projectiveValue_cubicJE h₅ hΔ a,
      projectiveValue_cubicJE h₅ hΔ b, e, val_mul, map_add]
    rfl)

theorem readComplexCubic_eq (h₅ : 5 ≤ ell) (hΔ : ¬ (ell : ℤ) ∣ W₀.Δ)
    (a : complexBase ⟶ (generic (LocalIntegers ell) ℚ).obj (detE ell W₀)) :
    haveI : (W₀⁄ℚ).IsElliptic := detRational_isElliptic hΔ
    (readComplexCubic h₅ hΔ a).toAdd =
      PreparedParam.projectiveValue (a.left ≫ (cubicJE h₅ hΔ).hom.left) := by
  let _ := weierstrassModelGrp ell h₅ W₀ hΔ
  rfl

#print axioms projectiveValue_eq_fieldValue
#print axioms fieldValue_eqToHom
#print axioms cubicJE
#print axioms projectiveValue_cubicJE
#print axioms readComplexCubic
#print axioms readComplexCubic_eq

end ZInQ.Manuscript.RC.ModelTarget
