import ZInQKernel.Contrib.OneProof.QuotientP1.P1ModelC

/-!
# p1-quot3, L4 part D: the projective line over `ℤ_(p)` by charts (scratch)

p1-quot's `QuotientP1/P1Scheme.lean` with the base `Spec ℚ` replaced by `Spec R` for any commutative ring `R`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.ProjectiveLine
open QuotientP1Proof (I i0 i1 i0_ne_i1 i1_ne_i0)

namespace HDec.MCRGlue.P1Model.PR

open LeafQM.AV

variable (R : Type) [CommRing R]

abbrev SR : Scheme.{0} := Spec (CommRingCat.of R)
abbrev LR : Scheme.{0} := ProjectiveSpace I (SR R)
abbrev stdR (i : I) : (LR R).Opens := standardOpen I (SR R) i


/-- Preimages of the standard opens under a normalized point. -/
theorem normalized_preimage_other {W : Scheme.{0}} (s : W ⟶ (SR R)) {i j : I} (hij : i ≠ j)
    (a : Γ(W, ⊤)) : normalized s i a ⁻¹ᵁ stdR R j = W.basicOpen a := by
  rw [normalized, homOfSections_preimage_standardOpen]
  simp [normalizedSections, hij.symm]

theorem normalized_preimage_self {W : Scheme.{0}} (s : W ⟶ (SR R)) (i : I) (a : Γ(W, ⊤)) :
    normalized s i a ⁻¹ᵁ stdR R i = ⊤ := by
  rw [normalized, homOfSections_preimage_standardOpen]
  simp [normalizedSections, Scheme.basicOpen_of_isUnit _ isUnit_one]

/-- Pulling back the chart coordinate along a normalized point. -/
theorem normalized_appLE {W : Scheme.{0}} (s : W ⟶ (SR R)) {i j : I} (hij : i ≠ j) (a : Γ(W, ⊤))
    (h : ⊤ ≤ normalized s i a ⁻¹ᵁ stdR R i) :
    (normalized s i a).appLE (stdR R i) ⊤ h (coordRatio I (SR R) i j) = a := by
  have := homOfSections_appLE_coordRatio s (normalizedSections i a) (normalizedSections_span i a)
    (coordinate := i) (by simp [normalizedSections]) j h
  refine this.trans ?_
  simp [normalizedSections, hij.symm]

theorem topIso_inv_coordRatio {i j : I} (hij : i ≠ j) :
    (stdR R i).topIso.inv (coordRatio I (SR R) i j) = relativeChartCoordinate (SR R) i := by
  have e := relativeChart_ι_eq_normalized (SR R) i
  have h : ⊤ ≤ (stdR R i).ι ⁻¹ᵁ stdR R i := by
    intro x _; exact x.2
  have h2 := congrArg (fun φ => φ (coordRatio I (SR R) i j)) (QuotientP1Proof.appLE_eq_of_eq' e (stdR R i) ⊤ h)
  have h3 := h2.trans (normalized_appLE R _ hij _ _)
  refine Eq.trans ?_ h3
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  rfl

theorem std_cover : stdR R i0 ⊔ stdR R i1 = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← iSup_standardOpen I (SR R)]
  refine iSup_le fun i => ?_
  rcases i with ⟨i⟩
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

/-- The basic open of a chart coordinate is the intersection of the two charts. -/
theorem basicOpen_coordRatio {i j : I} (hij : i ≠ j) :
    (LR R).basicOpen (coordRatio I (SR R) i j) = stdR R i ⊓ stdR R j := by
  rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv, topIso_inv_coordRatio R hij]
  have e := relativeChart_ι_eq_normalized (SR R) i
  have hpre : (stdR R i).ι ⁻¹ᵁ stdR R j = (stdR R i).toScheme.basicOpen (relativeChartCoordinate (SR R) i) := by
    rw [e]; exact normalized_preimage_other R _ hij _
  rw [← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

theorem coordRatio_mul :
    (LR R).presheaf.map (homOfLE (inf_le_left : stdR R i0 ⊓ stdR R i1 ≤ stdR R i0)).op (coordRatio I (SR R) i0 i1) *
      (LR R).presheaf.map (homOfLE (inf_le_right : stdR R i0 ⊓ stdR R i1 ≤ stdR R i1)).op
        (coordRatio I (SR R) i1 i0) = 1 := by
  have h := relativeChartCoordinate_mul (base := (SR R)) i0 i1 i0_ne_i1
    ((LR R).homOfLE (inf_le_left : stdR R i0 ⊓ stdR R i1 ≤ stdR R i0))
    ((LR R).homOfLE (inf_le_right : stdR R i0 ⊓ stdR R i1 ≤ stdR R i1)) (by simp)
  rw [← topIso_inv_coordRatio R i0_ne_i1, ← topIso_inv_coordRatio R i1_ne_i0,
    Scheme.homOfLE_appTop_topIso_inv, Scheme.homOfLE_appTop_topIso_inv, ← map_mul] at h
  have h2 := congrArg (stdR R i0 ⊓ stdR R i1).topIso.hom h
  rw [map_one] at h2
  simpa only [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] using h2

/-- **The chart description of the projective line over `ℚ`.** -/
def tau : ToP1 (LR R) where
  U := stdR R i0
  V := stdR R i1
  cover := std_cover R
  f := coordRatio I (SR R) i0 i1
  g := coordRatio I (SR R) i1 i0
  inv := coordRatio_mul R
  basicOpen_f := basicOpen_coordRatio R i0_ne_i1
  basicOpen_g := by rw [basicOpen_coordRatio R i1_ne_i0, inf_comm]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance smooth_L : SmoothOfRelativeDimension 1 (LR R ↘ (SR R)) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top (stdR R) (iSup_standardOpen I (SR R))
  intro i
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)
    (standardOpenIso I (SR R) i).inv, standardOpenIso_inv_ι_over]
  apply AffineSpace.smoothOfRelativeDimension_of_card_eq
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp

instance proper_L : IsProper (LR R ↘ (SR R)) := inferInstance

section Cover

variable {X : Scheme.{0}} (σ : ToP1 X)

open QuotientP1Proof (zOpens zRatio zCover zSpan zRatio_self appLE_eq_of_eq' topIso_inv_appLE' app_eq_of_appLE)

/-- The morphism `X → P¹` defined by `σ`. -/
def zHom (s : X ⟶ (SR R)) : X ⟶ LR R := (zCover σ).hom (zCover σ).coord (zSpan σ) s

theorem zHom_over (s : X ⟶ (SR R)) : zHom R σ s ≫ LR R ↘ (SR R) = s := Scheme.CoordinateCover.hom_over _ _ _

theorem zHom_preimage0 (s : X ⟶ (SR R)) : zHom R σ s ⁻¹ᵁ stdR R i0 = σ.U := by
  rw [zHom, Scheme.CoordinateCover.preimage_hom_standardOpen]
  refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le i0 ?_)
  · rcases i with ⟨i⟩; fin_cases i
    · exact X.basicOpen_le _
    · change X.basicOpen σ.g ≤ σ.U
      rw [σ.basicOpen_g]; exact inf_le_left
  · change σ.U ≤ X.basicOpen (1 : Γ(X, σ.U))
    rw [Scheme.basicOpen_of_isUnit _ isUnit_one]

theorem zHom_preimage1 (s : X ⟶ (SR R)) : zHom R σ s ⁻¹ᵁ stdR R i1 = σ.V := by
  rw [zHom, Scheme.CoordinateCover.preimage_hom_standardOpen]
  refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le i1 ?_)
  · rcases i with ⟨i⟩; fin_cases i
    · change X.basicOpen σ.f ≤ σ.V
      rw [σ.basicOpen_f]; exact inf_le_right
    · exact X.basicOpen_le _
  · change σ.V ≤ X.basicOpen (1 : Γ(X, σ.V))
    rw [Scheme.basicOpen_of_isUnit _ isUnit_one]

theorem zHom_appLE (s : X ⟶ (SR R)) (i j : I) (h : zOpens σ i ≤ zHom R σ s ⁻¹ᵁ stdR R i) :
    (zHom R σ s).appLE (stdR R i) (zOpens σ i) h (coordRatio I (SR R) i j) = zRatio σ i j := by
  apply (ConcreteCategory.bijective_of_isIso (zOpens σ i).topIso.inv).1
  rw [topIso_inv_appLE']
  have hι : (zOpens σ i).ι ≫ zHom R σ s = Scheme.CoordinateCover.localHom (zCover σ).coord (zSpan σ) s i :=
    Scheme.CoordinateCover.ι_hom _ _ _ i
  rw [appLE_eq_of_eq' hι]
  refine (homOfSections_appLE_coordRatio _ _ _ (coordinate := i) ?_ j _).trans ?_
  · change (zOpens σ i).topIso.inv (zRatio σ i i) = 1
    rw [zRatio_self, map_one]
  · rfl

end Cover

section Coord

open Polynomial

abbrev PRo : Over (SR R) := Over.mk (LR R ↘ (SR R))

open QuotientP1Proof (Nc)

/-- The polynomial ring onto the sections of a chart, through the chart isomorphism. -/
def chartPoly (i : I) : R[X] →+* Γ(LR R, stdR R i) :=
  ((stdR R i).topIso.hom.hom).comp ((standardOpenIso I (SR R) i).hom.appTop.hom.comp
    ((AffineSpace.SpecIso (Nc i) (CommRingCat.of R)).hom.appTop.hom.comp
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Nc i) R))).inv.hom.comp
        (MvPolynomial.uniqueAlgEquiv R (Nc i)).symm.toRingEquiv.toRingHom)))

theorem chartPoly_bijective (i : I) : Function.Bijective (chartPoly R i) := by
  unfold chartPoly
  simp only [RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (stdR R i).topIso.hom).comp
    ((ConcreteCategory.bijective_of_isIso (standardOpenIso I (SR R) i).hom.appTop).comp
      ((ConcreteCategory.bijective_of_isIso
          (AffineSpace.SpecIso (Nc i) (CommRingCat.of R)).hom.appTop).comp
        ((ConcreteCategory.bijective_of_isIso
            (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Nc i) R))).inv).comp
          (MvPolynomial.uniqueAlgEquiv R (Nc i)).symm.toRingEquiv.bijective)))

theorem chartPoly_X (i j : I) (hij : i ≠ j) :
    chartPoly R i (Polynomial.X : R[X]) = coordRatio I (SR R) i j := by
  have hd : (default : Nc i) = ⟨otherCoordinate i, otherCoordinate_ne i⟩ := Subsingleton.elim _ _
  simp only [chartPoly, RingHom.comp_apply]
  have h1 : (MvPolynomial.uniqueAlgEquiv R (Nc i)).symm.toRingEquiv.toRingHom Polynomial.X =
      MvPolynomial.X default := by
    simp [MvPolynomial.uniqueAlgEquiv]
  have h2 := AffineSpace.SpecIso_inv_appTop_coord (n := Nc i) (CommRingCat.of R)
    ⟨otherCoordinate i, otherCoordinate_ne i⟩
  have h3 : (AffineSpace.SpecIso (Nc i) (CommRingCat.of R)).hom.appTop
      ((AffineSpace.SpecIso (Nc i) (CommRingCat.of R)).inv.appTop
        (AffineSpace.coord (SR R) ⟨otherCoordinate i, otherCoordinate_ne i⟩)) =
      AffineSpace.coord (SR R) ⟨otherCoordinate i, otherCoordinate_ne i⟩ := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop,
      CommRingCat.id_apply]
  rw [h1, hd]
  erw [← h2, h3]
  change (stdR R i).topIso.hom (relativeChartCoordinate (SR R) i) = _
  rw [← topIso_inv_coordRatio R hij]
  exact Iso.inv_hom_id_apply _ _

theorem chartPoly_C (i : I) (c : R) :
    chartPoly R i (C c) = HDec.MCRGlue.baseToSectionsOver (CommRingCat.of R) (PRo R) (stdR R i) c := by
  simp only [chartPoly, RingHom.comp_apply]
  have h1 : (MvPolynomial.uniqueAlgEquiv R (Nc i)).symm.toRingEquiv.toRingHom (C c) =
      MvPolynomial.C c := by
    simp [MvPolynomial.uniqueAlgEquiv]
  rw [h1]
  set y := (Scheme.ΓSpecIso (CommRingCat.of R)).inv c with hy
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Nc i) R))).inv (MvPolynomial.C c) =
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Nc i) R))).appTop y := by
    rw [hy, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have h3 : (AffineSpace.SpecIso (Nc i) (CommRingCat.of R)).hom ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Nc i) R)) =
      AffineSpace (Nc i) (SR R) ↘ (SR R) := by
    have h := AffineSpace.SpecIso_inv_over (n := Nc i) (CommRingCat.of R)
    refine Eq.trans ?_ (Iso.hom_inv_id_assoc (AffineSpace.SpecIso (Nc i) (CommRingCat.of R))
      (AffineSpace (Nc i) (SR R) ↘ (SR R)))
    exact congrArg _ h.symm
  have h4 : (AffineSpace.SpecIso (Nc i) (CommRingCat.of R)).hom.appTop
      ((Spec.map (CommRingCat.ofHom (MvPolynomial.C : R →+* MvPolynomial (Nc i) R))).appTop y) =
      (AffineSpace (Nc i) (SR R) ↘ (SR R)).appTop y := by
    rw [← h3, Scheme.Hom.comp_appTop]; rfl
  have h5 : (standardOpenIso I (SR R) i).hom.appTop ((AffineSpace (Nc i) (SR R) ↘ (SR R)).appTop y) =
      (stdR R i).ι.appTop ((LR R ↘ (SR R)).appTop y) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, standardOpenIso_hom_over,
      Scheme.Hom.comp_appTop]; rfl
  erw [h2, h4, h5, QuotientP1Proof.topIso_hom_ι_appTop]
  rfl

theorem chart_bijective (i j : I) (hij : i ≠ j) :
    Function.Bijective (eval₂RingHom (HDec.MCRGlue.baseToSectionsOver (CommRingCat.of R) (PRo R) (stdR R i))
      (coordRatio I (SR R) i j)) := by
  have : eval₂RingHom (HDec.MCRGlue.baseToSectionsOver (CommRingCat.of R) (PRo R) (stdR R i)) (coordRatio I (SR R) i j) =
      chartPoly R i := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]; exact (chartPoly_C R i c).symm
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]; exact (chartPoly_X R i j hij).symm
  rw [this]; exact chartPoly_bijective R i

end Coord

end HDec.MCRGlue.P1Model.PR
