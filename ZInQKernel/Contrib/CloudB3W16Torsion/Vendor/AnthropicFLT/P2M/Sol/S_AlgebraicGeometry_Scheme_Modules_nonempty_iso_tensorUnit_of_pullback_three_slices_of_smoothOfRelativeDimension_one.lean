/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_exists_representsRelSubPic_algEquivZeroCut_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_eq_pullback_snd_comp_of_isProper
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one

set_option autoImplicit false

universe u

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry.RelPicard
open NeronModelInfra
open GoodReductionJacobian

namespace P2mCubeCurve

section Triv

variable {S T V : Scheme.{u}}

def Triv (φ : S ⟶ T) (A : T.Modules) : Prop :=
  Nonempty ((Scheme.Modules.pullback φ).obj A ≅ 𝟙_ _)

theorem triv_congr {φ ψ : S ⟶ T} (h : φ = ψ) (A : T.Modules) : Triv φ A ↔ Triv ψ A := by
  subst h; exact Iff.rfl

theorem triv_comp_iff (φ : S ⟶ T) (ψ : T ⟶ V) (A : V.Modules) :
    Triv (φ ≫ ψ) A ↔ Triv φ ((Scheme.Modules.pullback ψ).obj A) :=
  ⟨fun h => ⟨(Scheme.Modules.pullbackComp φ ψ).app A ≪≫ h.some⟩,
    fun h => ⟨((Scheme.Modules.pullbackComp φ ψ).app A).symm ≪≫ h.some⟩⟩

theorem Triv.of_iso_unit (φ : S ⟶ T) {A : T.Modules} (e : A ≅ 𝟙_ _) : Triv φ A :=
  ⟨(Scheme.Modules.pullback φ).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso φ⟩

theorem Triv.comp (φ : S ⟶ T) {ψ : T ⟶ V} {A : V.Modules} (h : Triv ψ A) : Triv (φ ≫ ψ) A :=
  (triv_comp_iff φ ψ A).mpr (Triv.of_iso_unit φ h.some)

theorem triv_id_iff (A : T.Modules) : Triv (𝟙 T) A ↔ Nonempty (A ≅ 𝟙_ _) :=
  ⟨fun h => ⟨((Scheme.Modules.pullbackId T).app A).symm ≪≫ h.some⟩,
    fun h => ⟨(Scheme.Modules.pullbackId T).app A ≪≫ h.some⟩⟩

def pbComp (φ : S ⟶ T) (ψ : T ⟶ V) (A : V.Modules) :
    (Scheme.Modules.pullback (φ ≫ ψ)).obj A ≅
      (Scheme.Modules.pullback φ).obj ((Scheme.Modules.pullback ψ).obj A) :=
  ((Scheme.Modules.pullbackComp φ ψ).app A).symm

def pbCongr {φ ψ : S ⟶ T} (h : φ = ψ) (A : T.Modules) :
    (Scheme.Modules.pullback φ).obj A ≅ (Scheme.Modules.pullback ψ).obj A :=
  (Scheme.Modules.pullbackCongr h).app A

end Triv

section Slices

variable {k : Type u} [Field k]

-- CloudW16 port: expanded the source-local shorthand in its original lexical scope.

abbrev slice₁ (X W : Over (Spec (CommRingCat.of k))) (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) : W ⟶ X ⊗ W := lift (toUnit W ≫ x) (𝟙 W)

abbrev slice₂ (V Y W : Over (Spec (CommRingCat.of k))) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y) : V ⊗ W ⟶ V ⊗ Y ⊗ W :=
  lift (fst V W) (lift (toUnit (V ⊗ W) ≫ y) (snd V W))

abbrev slice₃ (V W Z : Over (Spec (CommRingCat.of k))) (z : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Z) : V ⊗ W ⟶ V ⊗ W ⊗ Z :=
  lift (fst V W) (lift (snd V W) (toUnit (V ⊗ W) ≫ z))

theorem whiskerLeft_whiskerLeft (C Y Z : Over (Spec (CommRingCat.of k))) (z : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Z) :
    C ◁ (Y ◁ z) = (C ◁ fst Y (𝟙_ (Over (Spec (CommRingCat.of k))))) ≫ slice₃ C Y Z z := by
  have hs : snd Y (𝟙_ (Over (Spec (CommRingCat.of k)))) = toUnit _ := toUnit_unique _ _
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp [hs]

theorem whiskerLeft_lift (C Y Z : Over (Spec (CommRingCat.of k))) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y) (z : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Z) :
    C ◁ (lift y z) = (C ◁ y) ≫ slice₃ C Y Z z := by
  have hs : snd C (𝟙_ (Over (Spec (CommRingCat.of k)))) = toUnit _ := toUnit_unique _ _
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · apply CartesianMonoidalCategory.hom_ext
    · simp
    · simp [hs]

theorem whiskerLeft_slice₁ (C Y Z : Over (Spec (CommRingCat.of k))) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y) :
    C ◁ slice₁ Y Z y = slice₂ C Y Z y := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · apply CartesianMonoidalCategory.hom_ext <;> simp

theorem lift_toUnit_eq (Y Z : Over (Spec (CommRingCat.of k))) (z : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Z) :
    lift (𝟙 Y) (toUnit Y ≫ z) = lift (𝟙 Y) (toUnit Y) ≫ (Y ◁ z) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp

theorem slice₁_left (X W : Over (Spec (CommRingCat.of k))) (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) :
    (slice₁ X W x).left = rigSection X.hom W.hom ⟨x.left, Over.w x⟩ := rfl

theorem whiskerLeft_left (Y : Over (Spec (CommRingCat.of k))) {T W : Over (Spec (CommRingCat.of k))} (τ : T ⟶ W) :
    (Y ◁ τ).left = baseChangeSnd Y.hom (⟨τ.left, Over.w τ⟩ : SchemeHomOver T.hom W.hom) := rfl

end Slices

section InCut

variable {k : Type u} [Field k] {C T : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c} {t : T ⟶ Spec (CommRingCat.of k)}

theorem fibrewiseAlgEquivZero_of_pullbackAlong_point [LocallyOfFiniteType t] [GeometricallyIntegral t]
    (N : RigidifiedLineBundle c ε t) (τ₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) t)
    (h₀ : Nonempty ((N.pullbackAlong τ₀).L ≅
      SheafOfModules.unit (pullback c (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf)) :
    FibrewiseAlgEquivZero N := by
  intro K _ _ s
  change IsAlgEquivZero (pullback.snd (pullback.snd c t) s)
    ((Scheme.Modules.pullback (pullback.fst (pullback.snd c t) s)).obj N.L)
  obtain ⟨σ, hσ⟩ : ∃ σ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k), s ≫ t = σ := ⟨_, rfl⟩

  have cCT : pullback.fst c t ≫ c = pullback.snd c t ≫ t := pullback.condition
  have cA : pullback.fst (pullback.snd c t) s ≫ pullback.snd c t = pullback.snd (pullback.snd c t) s ≫ s :=
    pullback.condition
  have cT' : pullback.fst t σ ≫ t = pullback.snd t σ ≫ σ := pullback.condition
  have cAh : pullback.fst (pullback.snd (pullback.snd c t) s) (pullback.snd t σ) ≫ pullback.snd (pullback.snd c t) s =
      pullback.snd (pullback.snd (pullback.snd c t) s) (pullback.snd t σ) ≫ pullback.snd t σ := pullback.condition
  have cA1 : pullback.fst (pullback.snd (pullback.snd c t) s) (𝟙 (Spec (CommRingCat.of K))) ≫
      pullback.snd (pullback.snd c t) s =
      pullback.snd (pullback.snd (pullback.snd c t) s) (𝟙 (Spec (CommRingCat.of K))) ≫ 𝟙 _ := pullback.condition

  have hw : (pullback.fst (pullback.snd (pullback.snd c t) s) (pullback.snd t σ) ≫
      pullback.fst (pullback.snd c t) s ≫ pullback.fst c t) ≫ c =
      (pullback.snd (pullback.snd (pullback.snd c t) s) (pullback.snd t σ) ≫ pullback.fst t σ) ≫ t := by
    simp only [Category.assoc]
    rw [cCT, reassoc_of% cA, hσ, reassoc_of% cAh, cT']
  let Pm : pullback (pullback.snd (pullback.snd c t) s) (pullback.snd t σ) ⟶ pullback c t :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst (pullback.snd c t) s ≫ pullback.fst c t)
      (pullback.snd _ _ ≫ pullback.fst t σ) hw

  let t₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (pullback.snd t σ) :=
    ⟨pullback.lift s (𝟙 _) (by rw [hσ, Category.id_comp]), pullback.lift_snd _ _ _⟩
  let t₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) (pullback.snd t σ) :=
    ⟨pullback.lift (σ ≫ τ₀.1) (𝟙 _) (by rw [Category.assoc, τ₀.2, Category.comp_id, Category.id_comp]),
      pullback.lift_snd _ _ _⟩

  have hρ : (pullback.fst (pullback.snd (pullback.snd c t) s) (𝟙 (Spec (CommRingCat.of K))) ≫
      pullback.fst (pullback.snd c t) s ≫ pullback.fst c t) ≫ c =
      (pullback.snd (pullback.snd (pullback.snd c t) s) (𝟙 (Spec (CommRingCat.of K))) ≫ σ) ≫ 𝟙 _ := by
    simp only [Category.assoc, Category.comp_id]
    rw [cCT, reassoc_of% cA, hσ, reassoc_of% cA1]
  let rho : pullback (pullback.snd (pullback.snd c t) s) (𝟙 (Spec (CommRingCat.of K))) ⟶
      pullback c (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst (pullback.snd c t) s ≫ pullback.fst c t)
      (pullback.snd _ _ ≫ σ) hρ
  have E0 : baseChangeSnd (pullback.snd (pullback.snd c t) s) t₀ ≫ Pm = rho ≫ baseChangeSnd c τ₀ := by
    apply pullback.hom_ext <;>
      simp only [baseChangeSnd, Pm, rho, t₀, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]
  have E1 : baseChangeSnd (pullback.snd (pullback.snd c t) s) t₁ ≫ Pm =
      pullback.fst (pullback.snd (pullback.snd c t) s) (𝟙 (Spec (CommRingCat.of K))) ≫
        pullback.fst (pullback.snd c t) s := by
    apply pullback.hom_ext
    · simp only [baseChangeSnd, Pm, t₁, Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc,
        Category.id_comp]
    · simp only [baseChangeSnd, Pm, t₁, Category.assoc, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc]
      rw [cA, reassoc_of% cA1]
  refine ⟨pullback t σ, pullback.snd t σ, inferInstance, inferInstance, (Scheme.Modules.pullback Pm).obj N.L,
    N.isInvertible.pullback Pm, t₀, t₁, ⟨?_⟩, ⟨?_⟩⟩
  · exact (pbComp _ _ N.L).symm ≪≫ pbCongr E0 N.L ≪≫ pbComp _ _ N.L ≪≫
      (Scheme.Modules.pullback rho).mapIso h₀.some ≪≫ Scheme.Modules.pullbackUnitIso rho
  · exact (pbComp _ _ N.L).symm ≪≫ pbCongr E1 N.L ≪≫ pbComp _ _ N.L

end InCut

section Classify

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {P : SubPicCondition c ε} {D : RelativePic0Designation R c}

def pullbackAlongPostCompIso {T T' T'' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {t'' : T'' ⟶ Spec (CommRingCat.of R)}
    (N : RigidifiedLineBundle c ε t) (φ : SchemeHomOver t' t) (ψ : SchemeHomOver t'' t') :
    (N.pullbackAlong (postComp φ ψ)).L ≅ ((N.pullbackAlong φ).pullbackAlong ψ).L :=
  pbCongr (baseChangeSnd_comp c φ ψ).symm N.L ≪≫ pbComp _ _ N.L

theorem poincare_pullbackAlong_trivial_of_eq (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} (g : SchemeHomOver t D.toBase) (hg : g.1 = t ≫ D.zeroSection) :
    Nonempty ((h.poincare.pullbackAlong g).L ≅ SheafOfModules.unit (pullback c t).ringCatSheaf) := by
  let z : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase := ⟨D.zeroSection, D.zeroSection_toBase⟩
  let τ : SchemeHomOver t (𝟙 (Spec (CommRingCat.of R))) := ⟨t, Category.comp_id t⟩
  have hg' : g = postComp z τ := Subtype.ext hg
  subst hg'
  obtain ⟨e⟩ := RigidifiedLineBundle.pullbackAlong_congr τ h.zero
  exact ⟨pullbackAlongPostCompIso h.poincare z τ ≪≫ e ≪≫ Scheme.Modules.pullbackUnitIso _⟩

theorem comp_classify_eq_zero (h : RepresentsRelSubPic c ε P D) {T T' : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (N : RigidifiedLineBundle c ε t) (hN : P.P t N) (ψ : SchemeHomOver t' t)
    (hψ : Nonempty ((N.pullbackAlong ψ).L ≅ SheafOfModules.unit (pullback c t').ringCatSheaf)) :
    ψ.1 ≫ (h.classify t N hN).1 = t' ≫ D.zeroSection := by
  let κ := h.classify t N hN
  let g₁ : SchemeHomOver t' D.toBase := postComp κ ψ
  let g₀ : SchemeHomOver t' D.toBase :=
    ⟨t' ≫ D.zeroSection, by rw [Category.assoc, D.zeroSection_toBase, Category.comp_id]⟩
  have hcl := h.classify_spec t N hN
  obtain ⟨e₁⟩ := RigidifiedLineBundle.pullbackAlong_congr ψ hcl
  obtain ⟨e₀⟩ := poincare_pullbackAlong_trivial_of_eq h g₀ rfl
  have := h.ext_of_iso t' g₁ g₀
    ⟨pullbackAlongPostCompIso h.poincare κ ψ ≪≫ e₁ ≪≫ hψ.some ≪≫ e₀.symm⟩
  exact congrArg Subtype.val this

end Classify

section Main

variable (k : Type u) [Field k] [IsAlgClosed k]

-- CloudW16 port: expanded the source-local shorthand in its original lexical scope.

variable (C Y Z : Over (Spec (CommRingCat.of k)))
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left] [IsProper Y.hom] [IsIntegral Y.left]
  [LocallyOfFiniteType Z.hom] [IsIntegral Z.left]
  (c₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (y₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y)
  (z₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Z)
  (L : (C ⊗ Y ⊗ Z).left.Modules) (hL : Scheme.Modules.IsInvertible L)
  (h₁ : Triv (slice₁ C (Y ⊗ Z) c₀).left L) (h₂ : Triv (slice₂ C Y Z y₀).left L)
  (h₃ : Triv (slice₃ C Y Z z₀).left L)

include hL h₁ h₂ h₃ in

theorem main : Nonempty (L ≅ 𝟙_ _) := by

  let c : C.left ⟶ (Spec (CommRingCat.of k)) := C.hom
  let T : Over (Spec (CommRingCat.of k)) := Y ⊗ Z
  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c := ⟨c₀.left, Over.w c₀⟩
  let M : RigidifiedLineBundle c ε T.hom := ⟨L, hL, h₁⟩

  haveI : LocallyOfFiniteType T.hom := by
    change LocallyOfFiniteType (pullback.fst Y.hom Z.hom ≫ Y.hom); infer_instance
  haveI : IsIntegral T.left := by
    have : GeometricallyIntegral Y.hom := geometricallyIntegral_of_isAlgClosed Y.hom
    have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
    have : LocallyOfFinitePresentation Y.hom := inferInstance
    change IsIntegral (pullback Y.hom Z.hom); infer_instance
  haveI : GeometricallyIntegral T.hom := geometricallyIntegral_of_isAlgClosed T.hom

  let τ₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ T := lift y₀ z₀
  have hτ₀ : Triv (C ◁ τ₀).left L := by
    have e : (C ◁ τ₀).left = ((C ◁ y₀) ≫ slice₃ C Y Z z₀).left := by rw [← whiskerLeft_lift]
    rw [triv_congr e L]
    exact Triv.comp _ h₃
  have hcut : (algEquivZeroCut c ε).P T.hom M :=
    fibrewiseAlgEquivZero_of_pullbackAlong_point M ⟨τ₀.left, Over.w τ₀⟩ hτ₀

  obtain ⟨D, ⟨hrep⟩, -, hDpr, -⟩ := exists_representsRelSubPic_algEquivZeroCut_of_isAlgClosed k c ε
  haveI : IsProper D.toBase := hDpr
  let κ : SchemeHomOver T.hom D.toBase := hrep.classify T.hom M hcut

  have hY : (Y ◁ z₀).left ≫ κ.1 = (Y ⊗ 𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ D.zeroSection := by
    refine comp_classify_eq_zero hrep M hcut ⟨(Y ◁ z₀).left, Over.w _⟩ ?_
    change Triv (C ◁ (Y ◁ z₀)).left L
    rw [whiskerLeft_whiskerLeft, Over.comp_left]
    exact Triv.comp _ h₃
  have hZ : (slice₁ Y Z y₀).left ≫ κ.1 = Z.hom ≫ D.zeroSection := by
    refine comp_classify_eq_zero hrep M hcut ⟨(slice₁ Y Z y₀).left, Over.w _⟩ ?_
    change Triv (C ◁ slice₁ Y Z y₀).left L
    rw [whiskerLeft_slice₁]
    exact h₂

  haveI : IsReduced (pullback Y.hom Z.hom) := by
    change IsReduced T.left; infer_instance
  have hcontr : (lift (𝟙 Y) (toUnit Y ≫ z₀) : Y ⟶ Y ⊗ Z).left ≫ κ.1 = Y.hom ≫ D.zeroSection := by
    rw [lift_toUnit_eq, Over.comp_left, Category.assoc, hY, ← Category.assoc]
    congr 1
    exact Over.w (lift (𝟙 Y) (toUnit Y))
  obtain ⟨g, hg⟩ := exists_eq_pullback_snd_comp_of_isProper Y.hom Z.hom D.toBase κ.1 κ.2
    z₀.left (Over.w z₀) D.zeroSection hcontr

  have hgz : g = Z.hom ≫ D.zeroSection := by
    have e : (slice₁ Y Z y₀).left ≫ pullback.snd Y.hom Z.hom = 𝟙 _ := by
      change (slice₁ Y Z y₀ ≫ snd Y Z).left = (𝟙 Z : Z ⟶ Z).left
      rw [CartesianMonoidalCategory.lift_snd]
    have e1 : (slice₁ Y Z y₀).left ≫ κ.1 = ((slice₁ Y Z y₀).left ≫ pullback.snd Y.hom Z.hom) ≫ g := by
      rw [hg]; exact (Category.assoc _ _ _).symm
    rw [e, Category.id_comp] at e1
    exact e1.symm.trans hZ
  have hκ : κ.1 = T.hom ≫ D.zeroSection := by
    rw [hg, hgz]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ D.zeroSection) (Over.w (snd Y Z)))

  obtain ⟨e₁⟩ := hrep.classify_spec T.hom M hcut
  obtain ⟨e₀⟩ := poincare_pullbackAlong_trivial_of_eq hrep κ hκ
  exact ⟨e₁.symm ≪≫ e₀⟩

end Main

end P2mCubeCurve

end
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] (C Y Z : Over (Spec (CommRingCat.of k)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left] [IsProper Y.hom] [IsIntegral Y.left]
    [LocallyOfFiniteType Z.hom] [IsIntegral Z.left]
    (c₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) (y₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Z)
    (L : (C ⊗ Y ⊗ Z).left.Modules) (hL : Scheme.Modules.IsInvertible L)
    (h₁ : Nonempty ((Scheme.Modules.pullback
      (lift (toUnit (Y ⊗ Z) ≫ c₀) (𝟙 (Y ⊗ Z)) : Y ⊗ Z ⟶ C ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback
      (lift (fst C Z) (lift (toUnit (C ⊗ Z) ≫ y₀) (snd C Z)) : C ⊗ Z ⟶ C ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _))
    (h₃ : Nonempty ((Scheme.Modules.pullback
      (lift (fst C Y) (lift (snd C Y) (toUnit (C ⊗ Y) ≫ z₀)) : C ⊗ Y ⟶ C ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _)) :
    Nonempty (L ≅ 𝟙_ _) :=
  P2mCubeCurve.main k C Y Z c₀ y₀ z₀ L hL h₁ h₂ h₃
