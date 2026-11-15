import ZInQKernel.HDecomp.QM.Pairs
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveLine.Geometry
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveLine.RelativeCoordinates
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.Invertible
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveSpace.CoordinateCover

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
open LeafQM.AV
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.ProjectiveLine

namespace P1Quot

abbrev I : Type := ULift.{0} (Fin 2)
abbrev i0 : I := ⟨0⟩
abbrev i1 : I := ⟨1⟩
abbrev SQ : Scheme.{0} := Spec (CommRingCat.of ℚ)
abbrev L : Scheme.{0} := ProjectiveSpace I SQ
abbrev std (i : I) : L.Opens := standardOpen I SQ i

theorem i0_ne_i1 : i0 ≠ i1 := by decide
theorem i1_ne_i0 : i1 ≠ i0 := by decide

theorem appLE_eq_of_eq' {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (V : Y.Opens) (U : X.Opens)
    (h : U ≤ f ⁻¹ᵁ V) : f.appLE V U h = g.appLE V U (e ▸ h) := by
  subst e; rfl

/-- Preimages of the standard opens under a normalized point. -/
theorem normalized_preimage_other {W : Scheme.{0}} (s : W ⟶ SQ) {i j : I} (hij : i ≠ j)
    (a : Γ(W, ⊤)) : normalized s i a ⁻¹ᵁ std j = W.basicOpen a := by
  rw [normalized, homOfSections_preimage_standardOpen]
  simp [normalizedSections, hij.symm]

theorem normalized_preimage_self {W : Scheme.{0}} (s : W ⟶ SQ) (i : I) (a : Γ(W, ⊤)) :
    normalized s i a ⁻¹ᵁ std i = ⊤ := by
  rw [normalized, homOfSections_preimage_standardOpen]
  simp [normalizedSections, Scheme.basicOpen_of_isUnit _ isUnit_one]

/-- Pulling back the chart coordinate along a normalized point. -/
theorem normalized_appLE {W : Scheme.{0}} (s : W ⟶ SQ) {i j : I} (hij : i ≠ j) (a : Γ(W, ⊤))
    (h : ⊤ ≤ normalized s i a ⁻¹ᵁ std i) :
    (normalized s i a).appLE (std i) ⊤ h (coordRatio I SQ i j) = a := by
  have := homOfSections_appLE_coordRatio s (normalizedSections i a) (normalizedSections_span i a)
    (coordinate := i) (by simp [normalizedSections]) j h
  refine this.trans ?_
  simp [normalizedSections, hij.symm]

theorem topIso_inv_coordRatio {i j : I} (hij : i ≠ j) :
    (std i).topIso.inv (coordRatio I SQ i j) = relativeChartCoordinate SQ i := by
  have e := relativeChart_ι_eq_normalized SQ i
  have h : ⊤ ≤ (std i).ι ⁻¹ᵁ std i := by
    intro x _; exact x.2
  have h2 := congrArg (fun φ => φ (coordRatio I SQ i j)) (appLE_eq_of_eq' e (std i) ⊤ h)
  have h3 := h2.trans (normalized_appLE _ hij _ _)
  refine Eq.trans ?_ h3
  simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
  rfl

theorem std_cover : std i0 ⊔ std i1 = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← iSup_standardOpen I SQ]
  refine iSup_le fun i => ?_
  rcases i with ⟨i⟩
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

/-- The basic open of a chart coordinate is the intersection of the two charts. -/
theorem basicOpen_coordRatio {i j : I} (hij : i ≠ j) :
    L.basicOpen (coordRatio I SQ i j) = std i ⊓ std j := by
  rw [← Scheme.Opens.ι_image_basicOpen_topIso_inv, topIso_inv_coordRatio hij]
  have e := relativeChart_ι_eq_normalized SQ i
  have hpre : (std i).ι ⁻¹ᵁ std j = (std i).toScheme.basicOpen (relativeChartCoordinate SQ i) := by
    rw [e]; exact normalized_preimage_other _ hij _
  rw [← hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

theorem coordRatio_mul :
    L.presheaf.map (homOfLE (inf_le_left : std i0 ⊓ std i1 ≤ std i0)).op (coordRatio I SQ i0 i1) *
      L.presheaf.map (homOfLE (inf_le_right : std i0 ⊓ std i1 ≤ std i1)).op
        (coordRatio I SQ i1 i0) = 1 := by
  have h := relativeChartCoordinate_mul (base := SQ) i0 i1 i0_ne_i1
    (L.homOfLE (inf_le_left : std i0 ⊓ std i1 ≤ std i0))
    (L.homOfLE (inf_le_right : std i0 ⊓ std i1 ≤ std i1)) (by simp)
  rw [← topIso_inv_coordRatio i0_ne_i1, ← topIso_inv_coordRatio i1_ne_i0,
    Scheme.homOfLE_appTop_topIso_inv, Scheme.homOfLE_appTop_topIso_inv, ← map_mul] at h
  have h2 := congrArg (std i0 ⊓ std i1).topIso.hom h
  rw [map_one] at h2
  simpa only [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply] using h2

/-- **The chart description of the projective line over `ℚ`.** -/
def tau : ToP1 L where
  U := std i0
  V := std i1
  cover := std_cover
  f := coordRatio I SQ i0 i1
  g := coordRatio I SQ i1 i0
  inv := coordRatio_mul
  basicOpen_f := basicOpen_coordRatio i0_ne_i1
  basicOpen_g := by rw [basicOpen_coordRatio i1_ne_i0, inf_comm]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
instance smooth_L : SmoothOfRelativeDimension 1 (L ↘ SQ) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top std (iSup_standardOpen I SQ)
  intro i
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)
    (standardOpenIso I SQ i).inv, standardOpenIso_inv_ι_over]
  apply AffineSpace.smoothOfRelativeDimension_of_card_eq
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp

instance proper_L : IsProper (L ↘ SQ) := inferInstance

section Cover

variable {X : Scheme.{0}} (σ : ToP1 X)

/-- The two chart opens of `σ`, indexed like the homogeneous coordinates. -/
def zOpens : I → X.Opens
  | ⟨0⟩ => σ.U
  | ⟨1⟩ => σ.V

/-- The coordinate ratios `T_j / T_i` of `σ` on its charts. -/
def zRatio : (i j : I) → Γ(X, zOpens σ i)
  | ⟨0⟩, ⟨0⟩ => 1
  | ⟨0⟩, ⟨1⟩ => σ.f
  | ⟨1⟩, ⟨0⟩ => σ.g
  | ⟨1⟩, ⟨1⟩ => 1

theorem inv' : X.presheaf.map (homOfLE (inf_le_left : σ.V ⊓ σ.U ≤ σ.V)).op σ.g *
    X.presheaf.map (homOfLE (inf_le_right : σ.V ⊓ σ.U ≤ σ.U)).op σ.f = 1 := by
  have h := congrArg (X.presheaf.map (homOfLE (le_of_eq (inf_comm σ.V σ.U))).op) σ.inv
  rw [map_mul, Scheme.presheaf_map_map, Scheme.presheaf_map_map, map_one] at h
  rw [mul_comm]; exact h

theorem zRatio_self (i : I) : zRatio σ i i = 1 := by
  rcases i with ⟨i⟩; fin_cases i <;> rfl

theorem I_eq_of_ne {i j k : I} (hij : i ≠ j) (hjk : j ≠ k) : k = i := by
  rcases i with ⟨i⟩; rcases j with ⟨j⟩; rcases k with ⟨k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all

/-- The coordinate cover of `X` given by `σ`. -/
def zCover : X.CoordinateCover I where
  opens := zOpens σ
  ratio := zRatio σ
  ratio_self := zRatio_self σ
  basicOpen_ratio i j := by
    by_cases hij : i = j
    · subst hij; rw [zRatio_self, inf_idem]; exact X.basicOpen_of_isUnit isUnit_one
    rcases i with ⟨i⟩; rcases j with ⟨j⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact σ.basicOpen_f
    · rw [inf_comm]; exact σ.basicOpen_g
    · exact absurd rfl hij
  ratio_mul i j k := by
    by_cases hij : i = j
    · subst hij; rw [zRatio_self σ i, map_one, one_mul]
    by_cases hjk : j = k
    · subst hjk; rw [zRatio_self σ j, map_one, mul_one]
    obtain rfl := I_eq_of_ne hij hjk
    rw [zRatio_self σ k, map_one]
    rcases k with ⟨i⟩; rcases j with ⟨j⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact σ.inv.symm
    · exact (inv' σ).symm
    · exact absurd rfl hij
  iSup_U := by
    refine le_antisymm le_top ?_
    rw [← σ.cover]
    exact sup_le (le_iSup (zOpens σ) i0) (le_iSup (zOpens σ) i1)

theorem zSpan (i : I) : Ideal.span (Set.range fun k => ((zCover σ).coord k).localSection i) = ⊤ :=
  (Ideal.eq_top_iff_one _).mpr (Ideal.subset_span ⟨i, by simp [(zCover σ).ratio_self]⟩)

/-- The morphism `X → P¹` defined by `σ`. -/
def zHom (s : X ⟶ SQ) : X ⟶ L := (zCover σ).hom (zCover σ).coord (zSpan σ) s

theorem zHom_over (s : X ⟶ SQ) : zHom σ s ≫ L ↘ SQ = s := Scheme.CoordinateCover.hom_over _ _ _

theorem zHom_preimage0 (s : X ⟶ SQ) : zHom σ s ⁻¹ᵁ std i0 = σ.U := by
  rw [zHom, Scheme.CoordinateCover.preimage_hom_standardOpen]
  refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le i0 ?_)
  · rcases i with ⟨i⟩; fin_cases i
    · exact X.basicOpen_le _
    · change X.basicOpen σ.g ≤ σ.U
      rw [σ.basicOpen_g]; exact inf_le_left
  · change σ.U ≤ X.basicOpen (1 : Γ(X, σ.U))
    rw [Scheme.basicOpen_of_isUnit _ isUnit_one]

theorem zHom_preimage1 (s : X ⟶ SQ) : zHom σ s ⁻¹ᵁ std i1 = σ.V := by
  rw [zHom, Scheme.CoordinateCover.preimage_hom_standardOpen]
  refine le_antisymm (iSup_le fun i => ?_) (le_iSup_of_le i1 ?_)
  · rcases i with ⟨i⟩; fin_cases i
    · change X.basicOpen σ.f ≤ σ.V
      rw [σ.basicOpen_f]; exact inf_le_right
    · exact X.basicOpen_le _
  · change σ.V ≤ X.basicOpen (1 : Γ(X, σ.V))
    rw [Scheme.basicOpen_of_isUnit _ isUnit_one]

theorem topIso_inv_appLE' {X Y : Scheme.{0}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (h : U ≤ f ⁻¹ᵁ V) (x : Γ(Y, V)) :
    U.topIso.inv (f.appLE V U h x) =
      (U.ι ≫ f).appLE V ⊤ (by
        rw [Scheme.Hom.comp_preimage]
        exact fun localPoint _ ↦ h localPoint.2) x := by
  rw [Scheme.Hom.comp_appLE, Scheme.Opens.ι_appLE]
  simp only [Scheme.Hom.appLE, Scheme.Opens.topIso_inv]
  rw [← ConcreteCategory.comp_apply, Category.assoc, ← Functor.map_comp]
  rfl

/-- Converting `appLE` along an equality of opens into `app` followed by `eqToHom`. -/
theorem app_eq_of_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens)
    (e : f ⁻¹ᵁ V = U) (x : Γ(Y, V)) (y : Γ(X, U)) (h : f.appLE V U e.ge x = y) :
    f.app V x = X.presheaf.map (eqToHom e).op y := by
  subst h
  simp only [Scheme.Hom.appLE]
  rw [← ConcreteCategory.comp_apply, Category.assoc, ← Functor.map_comp]
  have : ((homOfLE e.ge).op ≫ (eqToHom e).op : (op (f ⁻¹ᵁ V) : X.Opensᵒᵖ) ⟶ op (f ⁻¹ᵁ V)) =
    𝟙 _ := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, Category.comp_id]

theorem zHom_appLE (s : X ⟶ SQ) (i j : I) (h : zOpens σ i ≤ zHom σ s ⁻¹ᵁ std i) :
    (zHom σ s).appLE (std i) (zOpens σ i) h (coordRatio I SQ i j) = zRatio σ i j := by
  apply (ConcreteCategory.bijective_of_isIso (zOpens σ i).topIso.inv).1
  rw [topIso_inv_appLE']
  have hι : (zOpens σ i).ι ≫ zHom σ s = Scheme.CoordinateCover.localHom (zCover σ).coord (zSpan σ) s i :=
    Scheme.CoordinateCover.ι_hom _ _ _ i
  rw [appLE_eq_of_eq' hι]
  refine (homOfSections_appLE_coordRatio _ _ _ (coordinate := i) ?_ j _).trans ?_
  · change (zOpens σ i).topIso.inv (zRatio σ i i) = 1
    rw [zRatio_self, map_one]
  · rfl

end Cover

section Coord

open Polynomial

/-- `MCRGlue.baseToSectionsOver`, verbatim (test copy). -/
def baseToSectionsOver (R : CommRingCat.{0}) (𝒵 : Over (Spec R)) (W : 𝒵.left.Opens) :
    R →+* Γ(𝒵.left, W) :=
  (𝒵.left.presheaf.map (homOfLE le_top).op).hom.comp
    ((𝒵.hom.appTop).hom.comp (Scheme.ΓSpecIso R).inv.hom)

abbrev PQ : Over SQ := Over.mk (L ↘ SQ)

abbrev Nc (i : I) : Type := {o : I // o ≠ i}

instance uniqueNc (i : I) : Unique (Nc i) where
  default := ⟨⟨i.down.rev⟩, by rcases i with ⟨i⟩; fin_cases i <;> decide⟩
  uniq := by
    rintro ⟨⟨o⟩, ho⟩
    rcases i with ⟨i⟩
    apply Subtype.ext
    fin_cases i <;> fin_cases o <;> first | exact absurd rfl ho | rfl

/-- The polynomial ring onto the sections of a chart, through the chart isomorphism. -/
def chartPoly (i : I) : ℚ[X] →+* Γ(L, std i) :=
  ((std i).topIso.hom.hom).comp ((standardOpenIso I SQ i).hom.appTop.hom.comp
    ((AffineSpace.SpecIso (Nc i) (CommRingCat.of ℚ)).hom.appTop.hom.comp
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Nc i) ℚ))).inv.hom.comp
        (MvPolynomial.uniqueAlgEquiv ℚ (Nc i)).symm.toRingEquiv.toRingHom)))

theorem chartPoly_bijective (i : I) : Function.Bijective (chartPoly i) := by
  unfold chartPoly
  simp only [RingHom.coe_comp]
  exact (ConcreteCategory.bijective_of_isIso (std i).topIso.hom).comp
    ((ConcreteCategory.bijective_of_isIso (standardOpenIso I SQ i).hom.appTop).comp
      ((ConcreteCategory.bijective_of_isIso
          (AffineSpace.SpecIso (Nc i) (CommRingCat.of ℚ)).hom.appTop).comp
        ((ConcreteCategory.bijective_of_isIso
            (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Nc i) ℚ))).inv).comp
          (MvPolynomial.uniqueAlgEquiv ℚ (Nc i)).symm.toRingEquiv.bijective)))

theorem topIso_hom_ι_appTop {X : Scheme.{0}} (U : X.Opens) (z : Γ(X, ⊤)) :
    U.topIso.hom (U.ι.appTop z) = X.presheaf.map (homOfLE le_top).op z := by
  simp only [Scheme.Opens.topIso_hom, Scheme.Hom.appTop, Scheme.Opens.ι_app]
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

theorem chartPoly_X (i j : I) (hij : i ≠ j) :
    chartPoly i (Polynomial.X : ℚ[X]) = coordRatio I SQ i j := by
  have hd : (default : Nc i) = ⟨otherCoordinate i, otherCoordinate_ne i⟩ := Subsingleton.elim _ _
  simp only [chartPoly, RingHom.comp_apply]
  have h1 : (MvPolynomial.uniqueAlgEquiv ℚ (Nc i)).symm.toRingEquiv.toRingHom Polynomial.X =
      MvPolynomial.X default := by
    simp [MvPolynomial.uniqueAlgEquiv]
  have h2 := AffineSpace.SpecIso_inv_appTop_coord (n := Nc i) (CommRingCat.of ℚ)
    ⟨otherCoordinate i, otherCoordinate_ne i⟩
  have h3 : (AffineSpace.SpecIso (Nc i) (CommRingCat.of ℚ)).hom.appTop
      ((AffineSpace.SpecIso (Nc i) (CommRingCat.of ℚ)).inv.appTop
        (AffineSpace.coord SQ ⟨otherCoordinate i, otherCoordinate_ne i⟩)) =
      AffineSpace.coord SQ ⟨otherCoordinate i, otherCoordinate_ne i⟩ := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop,
      CommRingCat.id_apply]
  rw [h1, hd]
  erw [← h2, h3]
  change (std i).topIso.hom (relativeChartCoordinate SQ i) = _
  rw [← topIso_inv_coordRatio hij]
  exact Iso.inv_hom_id_apply _ _

theorem chartPoly_C (i : I) (c : ℚ) :
    chartPoly i (C c) = baseToSectionsOver (CommRingCat.of ℚ) PQ (std i) c := by
  simp only [chartPoly, RingHom.comp_apply]
  have h1 : (MvPolynomial.uniqueAlgEquiv ℚ (Nc i)).symm.toRingEquiv.toRingHom (C c) =
      MvPolynomial.C c := by
    simp [MvPolynomial.uniqueAlgEquiv]
  rw [h1]
  set y := (Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv c with hy
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Nc i) ℚ))).inv (MvPolynomial.C c) =
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℚ →+* MvPolynomial (Nc i) ℚ))).appTop y := by
    rw [hy, ← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality]
    rfl
  have h3 : (AffineSpace.SpecIso (Nc i) (CommRingCat.of ℚ)).hom ≫
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℚ →+* MvPolynomial (Nc i) ℚ)) =
      AffineSpace (Nc i) SQ ↘ SQ := by
    have h := AffineSpace.SpecIso_inv_over (n := Nc i) (CommRingCat.of ℚ)
    refine Eq.trans ?_ (Iso.hom_inv_id_assoc (AffineSpace.SpecIso (Nc i) (CommRingCat.of ℚ))
      (AffineSpace (Nc i) SQ ↘ SQ))
    exact congrArg _ h.symm
  have h4 : (AffineSpace.SpecIso (Nc i) (CommRingCat.of ℚ)).hom.appTop
      ((Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℚ →+* MvPolynomial (Nc i) ℚ))).appTop y) =
      (AffineSpace (Nc i) SQ ↘ SQ).appTop y := by
    rw [← h3, Scheme.Hom.comp_appTop]; rfl
  have h5 : (standardOpenIso I SQ i).hom.appTop ((AffineSpace (Nc i) SQ ↘ SQ).appTop y) =
      (std i).ι.appTop ((L ↘ SQ).appTop y) := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, standardOpenIso_hom_over,
      Scheme.Hom.comp_appTop]; rfl
  erw [h2, h4, h5, topIso_hom_ι_appTop]
  rfl

theorem chart_bijective (i j : I) (hij : i ≠ j) :
    Function.Bijective (eval₂RingHom (baseToSectionsOver (CommRingCat.of ℚ) PQ (std i))
      (coordRatio I SQ i j)) := by
  have : eval₂RingHom (baseToSectionsOver (CommRingCat.of ℚ) PQ (std i)) (coordRatio I SQ i j) =
      chartPoly i := by
    refine Polynomial.ringHom_ext (fun c => ?_) ?_
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]; exact (chartPoly_C i c).symm
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]; exact (chartPoly_X i j hij).symm
  rw [this]; exact chartPoly_bijective i

/-- `MCRGlue.IsP1CoordinateQ`, verbatim (test copy). -/
def IsP1CoordinateQ (𝒵 : Over (Spec (CommRingCat.of ℚ))) (σ : ToP1 𝒵.left) : Prop :=
  IsAffineOpen σ.U ∧ IsAffineOpen σ.V ∧
    Function.Bijective (Polynomial.eval₂RingHom (baseToSectionsOver _ 𝒵 σ.U) σ.f) ∧
    Function.Bijective (Polynomial.eval₂RingHom (baseToSectionsOver _ 𝒵 σ.V) σ.g)

/-- `MCRQuot.P1SchemeQ`, verbatim (test copy). -/
def P1SchemeQ : Prop :=
  ∃ (P : Over (Spec (CommRingCat.of ℚ))) (τ : ToP1 P.left),
    IsProper P.hom ∧ SmoothOfRelativeDimension 1 P.hom ∧ IsP1CoordinateQ P τ ∧
    ∀ (Z : Over (Spec (CommRingCat.of ℚ))) (σ : ToP1 Z.left),
      ∃ (m : Z ⟶ P) (eU : m.left ⁻¹ᵁ τ.U = σ.U) (eV : m.left ⁻¹ᵁ τ.V = σ.V),
        m.left.app τ.U τ.f = Z.left.presheaf.map (eqToHom eU).op σ.f ∧
        m.left.app τ.V τ.g = Z.left.presheaf.map (eqToHom eV).op σ.g

theorem p1SchemeQ : P1SchemeQ := by
  refine ⟨PQ, tau, proper_L, smooth_L,
    ⟨isAffineOpen_standardOpen I SQ i0, isAffineOpen_standardOpen I SQ i1,
      chart_bijective i0 i1 i0_ne_i1, chart_bijective i1 i0 i1_ne_i0⟩, fun Z σ => ?_⟩
  refine ⟨Over.homMk (zHom σ Z.hom) (zHom_over σ Z.hom), zHom_preimage0 σ Z.hom,
    zHom_preimage1 σ Z.hom, ?_, ?_⟩
  · refine app_eq_of_appLE _ _ _ _ _ _ ?_
    exact zHom_appLE σ Z.hom i0 i1 (zHom_preimage0 σ Z.hom).ge
  · refine app_eq_of_appLE _ _ _ _ _ _ ?_
    exact zHom_appLE σ Z.hom i1 i0 (zHom_preimage1 σ Z.hom).ge

end Coord

end P1Quot

#print axioms P1Quot.p1SchemeQ
