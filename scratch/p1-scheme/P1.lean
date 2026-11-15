import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveLine.RelativeCoordinates
import ZInQKernel.HDecomp.QM.Pairs
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveLine.Geometry

noncomputable section

namespace GapGlue

open Polynomial CategoryTheory AlgebraicGeometry Limits LeafQM.AV
open TopologicalSpace Opposite

/-- Copied verbatim from `scratch/mcr-quot/MCRQuot.lean` L3989 (namespace `MCRGlue` there). -/
def baseToSectionsOver (R : CommRingCat.{0}) (𝒵 : Over (Spec R)) (W : 𝒵.left.Opens) :
    R →+* Γ(𝒵.left, W) :=
  (𝒵.left.presheaf.map (homOfLE le_top).op).hom.comp
    ((𝒵.hom.appTop).hom.comp (Scheme.ΓSpecIso R).inv.hom)

/-- Copied verbatim from `scratch/mcr-quot/MCRQuot.lean` L3995 (namespace `MCRGlue` there). -/
def IsP1CoordinateQ (𝒵 : Over (Spec (CommRingCat.of ℚ))) (σ : ToP1 𝒵.left) : Prop :=
  IsAffineOpen σ.U ∧ IsAffineOpen σ.V ∧
    Function.Bijective (eval₂RingHom (baseToSectionsOver _ 𝒵 σ.U) σ.f) ∧
    Function.Bijective (eval₂RingHom (baseToSectionsOver _ 𝒵 σ.V) σ.g)

/-- Copied verbatim from `scratch/mcr-quot/MCRQuot.lean` L8549 (namespace `MCRQuot` there). -/
def P1SchemeQ : Prop :=
  ∃ (P : Over (Spec (CommRingCat.of ℚ))) (τ : ToP1 P.left),
    IsProper P.hom ∧ SmoothOfRelativeDimension 1 P.hom ∧ IsP1CoordinateQ P τ ∧
    ∀ (Z : Over (Spec (CommRingCat.of ℚ))) (σ : ToP1 Z.left),
      ∃ (m : Z ⟶ P) (eU : m.left ⁻¹ᵁ τ.U = σ.U) (eV : m.left ⁻¹ᵁ τ.V = σ.V),
        m.left.app τ.U τ.f = Z.left.presheaf.map (eqToHom eU).op σ.f ∧
        m.left.app τ.V τ.g = Z.left.presheaf.map (eqToHom eV).op σ.g

/-! ## Restriction lemmas -/

section Restrict

variable {X : Scheme.{0}}

lemma presheaf_map_map {A B C D : X.Opens} (i : op A ⟶ op B) (j : op B ⟶ op D)
    (i' : op A ⟶ op C) (j' : op C ⟶ op D) (s : Γ(X, A)) :
    X.presheaf.map j (X.presheaf.map i s) = X.presheaf.map j' (X.presheaf.map i' s) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
  rfl

lemma homOfLE_appTop_topIso_inv {W U : X.Opens} (h : W ≤ U) (s : Γ(X, U)) :
    (X.homOfLE h).appTop (U.topIso.inv s) =
      W.topIso.inv (X.presheaf.map (homOfLE h).op s) := by
  simp only [Scheme.homOfLE_appTop, Scheme.Opens.topIso_inv]
  exact presheaf_map_map _ _ _ _ s

lemma image_basicOpen_topIso_inv (V : X.Opens) (s : Γ(X, V)) :
    V.ι ''ᵁ V.toScheme.basicOpen (V.topIso.inv s) = X.basicOpen s := by
  rw [Scheme.image_basicOpen, Scheme.Opens.ι_appIso]
  simp only [Iso.refl_inv, Scheme.Opens.topIso_inv]
  erw [Scheme.basicOpen_res]
  rw [Scheme.Opens.ι_image_top]
  exact inf_eq_right.mpr (X.basicOpen_le s)

lemma mem_basicOpen_topIso_inv (V : X.Opens) (s : Γ(X, V)) (p : V.toScheme) :
    p ∈ V.toScheme.basicOpen (V.topIso.inv s) ↔ p.1 ∈ X.basicOpen s := by
  rw [← image_basicOpen_topIso_inv V s]
  exact (Scheme.Opens.mem_ι_image_iff V).symm

end Restrict

/-! ## The relative line over `ℚ` -/

open ProjectiveSpace ProjectiveLine

local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "L" => ProjectiveLine.relativeLine (Spec (CommRingCat.of ℚ))

abbrev std (c : ULift.{0} (Fin 2)) : (L).Opens := standardOpen (ULift.{0} (Fin 2)) Q c

/-- The affine coordinate on the chart `c`, as a section of `P¹` over the chart. -/
def tcoord (c : ULift.{0} (Fin 2)) : Γ(L, std c) :=
  (std c).topIso.hom (relativeChartCoordinate Q c)

lemma topIso_inv_tcoord (c : ULift.{0} (Fin 2)) :
    (std c).topIso.inv (tcoord c) = relativeChartCoordinate Q c := by
  simp only [tcoord, Iso.hom_inv_id_apply]

lemma std_sup : std ⟨0⟩ ⊔ std ⟨1⟩ = ⊤ := by
  refine top_le_iff.mp ?_
  rw [← iSup_standardOpen (ULift.{0} (Fin 2)) Q]
  refine iSup_le fun ⟨c⟩ => ?_
  fin_cases c
  · exact le_sup_left
  · exact le_sup_right

lemma chart_preimage (c d : ULift.{0} (Fin 2)) (hcd : c ≠ d) :
    (std c).ι ⁻¹ᵁ std d = (std c).toScheme.basicOpen (relativeChartCoordinate Q c) := by
  conv_lhs => rw [relativeChart_ι_eq_normalized Q c]
  rw [normalized, homOfSections_preimage_standardOpen]
  simp [normalizedSections, hcd.symm]

lemma basicOpen_tcoord (c d : ULift.{0} (Fin 2)) (hcd : c ≠ d) :
    (L).basicOpen (tcoord c) = std c ⊓ std d := by
  rw [← image_basicOpen_topIso_inv, topIso_inv_tcoord, ← chart_preimage c d hcd,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]

lemma tcoord_mul (c d : ULift.{0} (Fin 2)) (hcd : c ≠ d) (h₁ : std c ⊓ std d ≤ std c)
    (h₂ : std c ⊓ std d ≤ std d) :
    (L).presheaf.map (homOfLE h₁).op (tcoord c) *
      (L).presheaf.map (homOfLE h₂).op (tcoord d) = 1 := by
  have key := relativeChartCoordinate_mul (base := Q) c d hcd ((L).homOfLE h₁) ((L).homOfLE h₂)
    (by rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι])
  rw [← topIso_inv_tcoord c, ← topIso_inv_tcoord d, homOfLE_appTop_topIso_inv,
    homOfLE_appTop_topIso_inv, ← map_mul] at key
  have := congrArg (std c ⊓ std d).topIso.hom key
  rwa [Iso.inv_hom_id_apply, map_one] at this

/-- The tautological map `P¹_ℚ → P¹` by charts. -/
def tau : ToP1 L where
  U := std ⟨0⟩
  V := std ⟨1⟩
  cover := std_sup
  f := tcoord ⟨0⟩
  g := tcoord ⟨1⟩
  inv := tcoord_mul _ _ (by decide) _ _
  basicOpen_f := basicOpen_tcoord _ _ (by decide)
  basicOpen_g := by rw [basicOpen_tcoord _ ⟨0⟩ (by decide), inf_comm]

lemma presheaf_map_map_self {X : Scheme.{0}} {A B : X.Opens} (i : op A ⟶ op B) (j : op B ⟶ op A)
    (s : Γ(X, A)) : X.presheaf.map j (X.presheaf.map i s) = s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp, show i ≫ j = 𝟙 _ from rfl,
    CategoryTheory.Functor.map_id, CommRingCat.id_apply]

/-! ## Smoothness and the chart rings -/

instance smooth_L : SmoothOfRelativeDimension 1 (L ↘ Q) := by
  apply IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 1) std
    (iSup_standardOpen (ULift.{0} (Fin 2)) Q)
  intro c
  rw [← standardOpenIso_hom_over,
    MorphismProperty.cancel_left_of_respectsIso (P := @SmoothOfRelativeDimension 1)]
  apply AffineSpace.smoothOfRelativeDimension_of_card_eq
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp

lemma bij_tcoord (c : ULift.{0} (Fin 2)) :
    Function.Bijective
      (eval₂RingHom (baseToSectionsOver _ (relativeLineOver ℚ) (std c)) (tcoord c)) := by
  let n := {i : ULift.{0} (Fin 2) // i ≠ c}
  let i₀ : n := ⟨otherCoordinate c, otherCoordinate_ne c⟩
  let eqv : PUnit.{1} ≃ n :=
    { toFun := fun _ => i₀, invFun := fun _ => PUnit.unit, left_inv := fun _ => rfl,
      right_inv := fun j => Subtype.ext (otherCoordinate_eq j.2.symm) }
  let R := CommRingCat.of ℚ
  let ι : (↑R)[X] ≃ₐ[ℚ] MvPolynomial n R :=
    (MvPolynomial.pUnitAlgEquiv.{0, 0} ℚ).symm.trans (MvPolynomial.renameEquiv ℚ eqv)
  let ev : MvPolynomial n R →+* Γ(𝔸(n; Spec R), ⊤) :=
    MvPolynomial.eval₂Hom ((Scheme.ΓSpecIso R).inv ≫ (𝔸(n; Spec R) ↘ Spec R).appTop).hom
      (AffineSpace.coord (Spec R))
  have hev : Function.Bijective ev := by
    have h : CommRingCat.ofHom ev =
        (Scheme.ΓSpecIso _).inv ≫ (AffineSpace.SpecIso n R).hom.appTop := by
      rw [AffineSpace.SpecIso_hom_appTop, Iso.inv_hom_id_assoc]
    have : IsIso (AffineSpace.SpecIso n R).hom.appTop :=
      inferInstanceAs (IsIso ((AffineSpace.SpecIso n R).hom.app ⊤))
    have : IsIso (CommRingCat.ofHom ev) := by rw [h]; infer_instance
    exact ConcreteCategory.bijective_of_isIso (CommRingCat.ofHom ev)
  let e2 := (standardOpenIso (ULift.{0} (Fin 2)) Q c).hom.appTop
  have : IsIso e2 := inferInstanceAs (IsIso ((standardOpenIso (ULift.{0} (Fin 2)) Q c).hom.app ⊤))
  have he2 : Function.Bijective e2 := ConcreteCategory.bijective_of_isIso _
  have he1 : Function.Bijective (std c).topIso.hom := ConcreteCategory.bijective_of_isIso _
  have hcomp : eval₂RingHom (baseToSectionsOver _ (relativeLineOver ℚ) (std c)) (tcoord c) =
      (std c).topIso.hom.hom.comp (e2.hom.comp (ev.comp ι.toRingEquiv.toRingHom)) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_rat _ _) ?_
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      AlgEquiv.toRingEquiv_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv]
    simp only [ι, AlgEquiv.trans_apply, MvPolynomial.pUnitAlgEquiv_symm_X,
      MvPolynomial.renameEquiv_apply, MvPolynomial.rename_X, ev, MvPolynomial.eval₂Hom_X']
    rfl
  rw [hcomp]
  exact he1.comp (he2.comp (hev.comp ι.bijective))

lemma isP1_tau : IsP1CoordinateQ (relativeLineOver ℚ) tau :=
  ⟨isAffineOpen_standardOpen _ _ _, isAffineOpen_standardOpen _ _ _, bij_tcoord _, bij_tcoord _⟩

/-! ## Gluing a map to `P¹` by charts -/

section Glue

variable {Z : Scheme.{0}} (str : Z ⟶ Q) (σ : ToP1 Z)

def opensOf : Bool → Z.Opens
  | true => σ.U
  | false => σ.V

def secOf : (b : Bool) → Γ(Z, opensOf σ b)
  | true => σ.f
  | false => σ.g

def coordOf : Bool → ULift.{0} (Fin 2)
  | true => ⟨0⟩
  | false => ⟨1⟩

lemma coordOf_ne {b b' : Bool} (h : b ≠ b') : coordOf b ≠ coordOf b' := by
  cases b <;> cases b' <;> first | exact absurd rfl h | decide

lemma basicOpen_secOf (b : Bool) : Z.basicOpen (secOf σ b) = σ.U ⊓ σ.V := by
  cases b
  · exact σ.basicOpen_g
  · exact σ.basicOpen_f

lemma opensOf_cover : IsOpenCover (opensOf σ) := by
  show iSup (opensOf σ) = ⊤
  rw [iSup_bool_eq]
  exact σ.cover

def cov : Z.OpenCover := Z.openCoverOfIsOpenCover (opensOf σ) (opensOf_cover σ)

def chartMap (b : Bool) : (opensOf σ b).toScheme ⟶ L :=
  normalized ((opensOf σ b).ι ≫ str) (coordOf b) ((opensOf σ b).topIso.inv (secOf σ b))

lemma key (A B : Z.Opens) (a : Γ(Z, A)) (b : Γ(Z, B)) (c d : ULift.{0} (Fin 2)) (hcd : c ≠ d)
    (hab : Z.presheaf.map (homOfLE (inf_le_left : A ⊓ B ≤ A)).op a *
      Z.presheaf.map (homOfLE (inf_le_right : A ⊓ B ≤ B)).op b = 1) :
    pullback.fst A.ι B.ι ≫ normalized (A.ι ≫ str) c (A.topIso.inv a) =
      pullback.snd A.ι B.ι ≫ normalized (B.ι ≫ str) d (B.topIso.inv b) := by
  rw [← cancel_epi (isPullback_opens_inf A B).isoPullback.hom,
    IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc,
    comp_normalized, comp_normalized, ← Category.assoc, ← Category.assoc,
    Scheme.homOfLE_ι, Scheme.homOfLE_ι, homOfLE_appTop_topIso_inv, homOfLE_appTop_topIso_inv]
  exact normalized_eq_of_mul_eq_one _ c d hcd _ _ (by rw [← map_mul, hab, map_one])

lemma compat (x y : Bool) :
    pullback.fst ((cov σ).f x) ((cov σ).f y) ≫ chartMap str σ x =
      pullback.snd ((cov σ).f x) ((cov σ).f y) ≫ chartMap str σ y := by
  change pullback.fst (opensOf σ x).ι (opensOf σ y).ι ≫ _ =
    pullback.snd (opensOf σ x).ι (opensOf σ y).ι ≫ _
  cases x <;> cases y
  · rw [(cancel_mono _).1 (pullback.condition (f := (opensOf σ false).ι)
      (g := (opensOf σ false).ι))]
  · rw [← pullbackSymmetry_hom_comp_snd, ← pullbackSymmetry_hom_comp_fst, Category.assoc,
      Category.assoc]
    exact congrArg ((pullbackSymmetry (opensOf σ false).ι (opensOf σ true).ι).hom ≫ ·)
      (key str σ.U σ.V σ.f σ.g ⟨0⟩ ⟨1⟩ (by decide) σ.inv).symm
  · exact key str σ.U σ.V σ.f σ.g ⟨0⟩ ⟨1⟩ (by decide) σ.inv
  · rw [(cancel_mono _).1 (pullback.condition (f := (opensOf σ true).ι)
      (g := (opensOf σ true).ι))]

def mleft : Z ⟶ L := (cov σ).glueMorphisms (chartMap str σ) (compat str σ)

lemma ι_mleft (b : Bool) : (opensOf σ b).ι ≫ mleft str σ = chartMap str σ b :=
  Scheme.Cover.ι_glueMorphisms (cov σ) _ _ b

lemma mleft_over : mleft str σ ≫ (L ↘ Q) = str := by
  refine (cov σ).hom_ext _ _ fun (b : Bool) => ?_
  change (opensOf σ b).ι ≫ _ = (opensOf σ b).ι ≫ _
  rw [reassoc_of% ι_mleft, chartMap, normalized_over]

lemma mem_iff_of_mem (b b' : Bool) (x : Z) (hx : x ∈ opensOf σ b') :
    mleft str σ x ∈ std (coordOf b) ↔ x ∈ opensOf σ b := by
  have e : mleft str σ x = chartMap str σ b' ⟨x, hx⟩ := by
    rw [← ι_mleft str σ b']
    rfl
  rw [e]
  change (⟨x, hx⟩ : (opensOf σ b').toScheme) ∈ chartMap str σ b' ⁻¹ᵁ std (coordOf b) ↔ _
  rw [chartMap, normalized, homOfSections_preimage_standardOpen]
  by_cases hb : b' = b
  · subst hb
    rw [normalizedSections, if_pos rfl, Scheme.basicOpen_of_isUnit _ isUnit_one]
    exact iff_of_true trivial hx
  · rw [normalizedSections, if_neg (coordOf_ne (Ne.symm hb))]
    refine (mem_basicOpen_topIso_inv (opensOf σ b') (secOf σ b') ⟨x, hx⟩).trans ?_
    rw [basicOpen_secOf]
    cases b <;> cases b' <;> simp_all [opensOf]

lemma preimage_std (b : Bool) : mleft str σ ⁻¹ᵁ std (coordOf b) = opensOf σ b := by
  ext x
  have hx : x ∈ σ.U ⊔ σ.V := by rw [σ.cover]; trivial
  change mleft str σ x ∈ std (coordOf b) ↔ x ∈ opensOf σ b
  rcases (Opens.mem_sup.mp hx) with h | h
  · exact mem_iff_of_mem str σ b true x h
  · exact mem_iff_of_mem str σ b false x h

lemma resLE_eq (b : Bool) :
    (mleft str σ).resLE (std (coordOf b)) (opensOf σ b) (preimage_std str σ b).ge =
      relativeChartPoint ((opensOf σ b).ι ≫ str) (coordOf b)
        ((opensOf σ b).topIso.inv (secOf σ b)) := by
  rw [← cancel_mono (std (coordOf b)).ι, Scheme.Hom.resLE_comp_ι, relativeChartPoint_ι,
    ι_mleft]
  rfl

lemma appLE_eq (b : Bool) :
    (mleft str σ).appLE (std (coordOf b)) (opensOf σ b) (preimage_std str σ b).ge
      (tcoord (coordOf b)) = secOf σ b := by
  have h := congrArg (fun φ => φ.appTop (relativeChartCoordinate Q (coordOf b)))
    (resLE_eq str σ b)
  simp only [relativeChartPoint_coordinate] at h
  erw [Scheme.Hom.resLE_app_top] at h
  simp only [CommRingCat.comp_apply] at h
  have := congrArg (opensOf σ b).topIso.hom h
  simpa only [Iso.inv_hom_id_apply] using this

lemma app_eq (b : Bool) :
    (mleft str σ).app (std (coordOf b)) (tcoord (coordOf b)) =
      Z.presheaf.map (eqToHom (preimage_std str σ b)).op (secOf σ b) := by
  rw [← appLE_eq str σ b, Scheme.Hom.appLE, CommRingCat.comp_apply, presheaf_map_map_self]

end Glue

/-- **`P1SchemeQ`** (mcr-quot's glue (B-P¹)): the relative projective line
`ℙ(ULift (Fin 2); Spec ℚ)` of the vendored CloudW07 library, with its two standard charts,
is proper and smooth of relative dimension 1 over `ℚ`, its charts are `Spec ℚ[t]`, `Spec ℚ[s]`,
and it represents maps to `P¹` given by charts. -/
theorem p1SchemeQ : P1SchemeQ := by
  refine ⟨relativeLineOver ℚ, tau, ?_, smooth_L, isP1_tau, ?_⟩
  · exact inferInstanceAs (IsProper (L ↘ Q))
  · intro Z σ
    exact ⟨Over.homMk (mleft Z.hom σ) (mleft_over Z.hom σ), preimage_std Z.hom σ true,
      preimage_std Z.hom σ false, app_eq Z.hom σ true, app_eq Z.hom σ false⟩

end GapGlue
