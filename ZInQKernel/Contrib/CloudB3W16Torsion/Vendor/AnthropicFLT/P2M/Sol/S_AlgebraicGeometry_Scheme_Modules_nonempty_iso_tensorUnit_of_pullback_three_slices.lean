/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_nonempty_iso_unit_of_forall_pullbackAlong_point
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_mem_of_isProper_of_forall_smoothProperCurve_mem
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices

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

namespace P2mCubeAssembly

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

end Triv

section Slices

variable {k : Type u} [Field k]

-- CloudW16 port: expanded the source-local shorthand in its original lexical scope.

abbrev slice₁ (X W : Over (Spec (CommRingCat.of k))) (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) : W ⟶ X ⊗ W := lift (toUnit W ≫ x) (𝟙 W)

abbrev slice₂ (V Y W : Over (Spec (CommRingCat.of k))) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y) : V ⊗ W ⟶ V ⊗ Y ⊗ W :=
  lift (fst V W) (lift (toUnit (V ⊗ W) ≫ y) (snd V W))

abbrev slice₃ (V W Z : Over (Spec (CommRingCat.of k))) (z : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Z) : V ⊗ W ⟶ V ⊗ W ⊗ Z :=
  lift (fst V W) (lift (snd V W) (toUnit (V ⊗ W) ≫ z))

abbrev swap (X Y Z : Over (Spec (CommRingCat.of k))) : Y ⊗ (X ⊗ Z) ⟶ X ⊗ (Y ⊗ Z) :=
  lift (snd _ _ ≫ fst _ _) (lift (fst _ _) (snd _ _ ≫ snd _ _))

theorem swap_swap (X Y Z : Over (Spec (CommRingCat.of k))) : swap Y X Z ≫ swap X Y Z = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · apply CartesianMonoidalCategory.hom_ext <;> simp

theorem slice₁_swap (X Y Z : Over (Spec (CommRingCat.of k))) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y) :
    slice₁ Y (X ⊗ Z) y ≫ swap X Y Z = slice₂ X Y Z y := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · apply CartesianMonoidalCategory.hom_ext <;> simp

theorem slice₁_whiskerRight {C X : Over (Spec (CommRingCat.of k))} (W : Over (Spec (CommRingCat.of k))) (ψ : C ⟶ X) (p : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C) :
    slice₁ C W p ≫ (ψ ▷ W) = slice₁ X W (p ≫ ψ) := by
  apply CartesianMonoidalCategory.hom_ext <;> simp

theorem slice₂_whiskerRight {C X : Over (Spec (CommRingCat.of k))} (Y Z : Over (Spec (CommRingCat.of k))) (ψ : C ⟶ X) (y : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y) :
    slice₂ C Y Z y ≫ (ψ ▷ (Y ⊗ Z)) = (ψ ▷ Z) ≫ slice₂ X Y Z y := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · apply CartesianMonoidalCategory.hom_ext <;> simp

theorem slice₃_whiskerRight {C X : Over (Spec (CommRingCat.of k))} (Y Z : Over (Spec (CommRingCat.of k))) (ψ : C ⟶ X) (z : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Z) :
    slice₃ C Y Z z ≫ (ψ ▷ (Y ⊗ Z)) = (ψ ▷ Y) ≫ slice₃ X Y Z z := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · apply CartesianMonoidalCategory.hom_ext <;> simp

theorem whiskerLeft_swap (X Y Z : Over (Spec (CommRingCat.of k))) (τ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X ⊗ Z) :
    (Y ◁ τ) ≫ swap X Y Z = (Y ◁ (τ ≫ snd X Z)) ≫ slice₁ X (Y ⊗ Z) (τ ≫ fst X Z) := by
  have hs : snd Y (𝟙_ (Over (Spec (CommRingCat.of k)))) = toUnit _ := toUnit_unique _ _
  apply CartesianMonoidalCategory.hom_ext
  · simp [hs]
  · apply CartesianMonoidalCategory.hom_ext <;> simp

theorem slice₁_left (X W : Over (Spec (CommRingCat.of k))) (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) :
    (slice₁ X W x).left = rigSection X.hom W.hom ⟨x.left, Over.w x⟩ := rfl

theorem whiskerLeft_left (Y : Over (Spec (CommRingCat.of k))) {T W : Over (Spec (CommRingCat.of k))} (τ : T ⟶ W) :
    (Y ◁ τ).left = baseChangeSnd Y.hom (⟨τ.left, Over.w τ⟩ : SchemeHomOver T.hom W.hom) := rfl

end Slices

section Main

variable (k : Type u) [Field k] [IsAlgClosed k]

-- CloudW16 port: expanded the source-local shorthand in its original lexical scope.

variable (X Y Z : Over (Spec (CommRingCat.of k)))
  [IsProper X.hom] [IsIntegral X.left] [IsProper Y.hom] [IsIntegral Y.left]
  [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsIntegral Z.left]
  (x₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) (y₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y)
  (z₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Z)
  (L : (X ⊗ Y ⊗ Z).left.Modules) (hL : Scheme.Modules.IsInvertible L)
  (h₁ : Triv (slice₁ X (Y ⊗ Z) x₀).left L) (h₂ : Triv (slice₂ X Y Z y₀).left L)
  (h₃ : Triv (slice₃ X Y Z z₀).left L)

include hL h₁ h₂ h₃ in
omit [IsSeparated Z.hom] [QuasiCompact Z.hom] in

theorem stepA (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) : Triv (slice₁ X (Y ⊗ Z) x).left L := by

  let S : Set ((Spec (CommRingCat.of k)) ⟶ X.left) := {x' | ∀ hx' : x' ≫ X.hom = 𝟙 _,
    Triv (rigSection X.hom (Y ⊗ Z).hom ⟨x', hx'⟩) L}
  have h0 : x₀.left ∈ S := fun _ => h₁
  suffices hx : x.left ∈ S from hx (Over.w x)
  refine mem_of_isProper_of_forall_smoothProperCurve_mem X.hom S x₀.left (Over.w x₀) h0 ?_ x.left (Over.w x)
  intro C c _ _ _ ψ hψ p q hp hq hpS hqX

  let C' : Over (Spec (CommRingCat.of k)) := Over.mk c
  let ψ' : C' ⟶ X := Over.homMk ψ hψ
  let p' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C' := Over.homMk p hp
  let q' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ C' := Over.homMk q hq
  let Φ : C' ⊗ Y ⊗ Z ⟶ X ⊗ Y ⊗ Z := ψ' ▷ (Y ⊗ Z)
  let L' : (C' ⊗ Y ⊗ Z).left.Modules := (Scheme.Modules.pullback Φ.left).obj L
  haveI : IsProper C'.hom := ‹IsProper c›
  haveI : SmoothOfRelativeDimension 1 C'.hom := ‹SmoothOfRelativeDimension 1 c›
  haveI : IsIntegral C'.left := ‹IsIntegral C›

  have h₁' : Triv (slice₁ C' (Y ⊗ Z) p').left L' := by
    show Triv _ ((Scheme.Modules.pullback Φ.left).obj L)
    rw [← triv_comp_iff, ← Over.comp_left, slice₁_whiskerRight]
    exact hpS (Over.w (p' ≫ ψ'))
  have h₂' : Triv (slice₂ C' Y Z y₀).left L' := by
    show Triv _ ((Scheme.Modules.pullback Φ.left).obj L)
    rw [← triv_comp_iff, ← Over.comp_left, slice₂_whiskerRight, Over.comp_left]
    exact Triv.comp _ h₂
  have h₃' : Triv (slice₃ C' Y Z z₀).left L' := by
    show Triv _ ((Scheme.Modules.pullback Φ.left).obj L)
    rw [← triv_comp_iff, ← Over.comp_left, slice₃_whiskerRight, Over.comp_left]
    exact Triv.comp _ h₃

  have key := Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices_of_smoothOfRelativeDimension_one
    k C' Y Z p' y₀ z₀ L' (hL.pullback _) h₁' h₂' h₃'

  have e : rigSection X.hom (Y ⊗ Z).hom ⟨q ≫ ψ, hqX⟩ = (slice₁ C' (Y ⊗ Z) q').left ≫ Φ.left := by
    rw [← Over.comp_left, slice₁_whiskerRight]; rfl
  rw [triv_congr e]
  exact (triv_comp_iff _ _ _).mpr (Triv.of_iso_unit _ key.some)

include hL h₁ h₂ h₃ in
omit [IsSeparated Z.hom] [QuasiCompact Z.hom] in

theorem main : Nonempty (L ≅ 𝟙_ _) := by

  let σ : Y ⊗ (X ⊗ Z) ⟶ X ⊗ (Y ⊗ Z) := swap X Y Z
  let Lt : (Limits.pullback Y.hom (X ⊗ Z).hom).Modules := (Scheme.Modules.pullback σ.left).obj L
  let ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) Y.hom := ⟨y₀.left, Over.w y₀⟩

  have hrig : Nonempty ((Scheme.Modules.pullback (rigSection Y.hom (X ⊗ Z).hom ε)).obj Lt ≅
      SheafOfModules.unit (X ⊗ Z).left.ringCatSheaf) := by
    have e : rigSection Y.hom (X ⊗ Z).hom ε ≫ σ.left = (slice₂ X Y Z y₀).left := by
      change (slice₁ Y (X ⊗ Z) y₀ ≫ σ).left = _
      rw [slice₁_swap]
    exact (triv_comp_iff _ _ _).mp ((triv_congr e L).mpr h₂)
  let M : RigidifiedLineBundle Y.hom ε (X ⊗ Z).hom := ⟨Lt, hL.pullback _, hrig⟩

  haveI : LocallyOfFiniteType (X ⊗ Z).hom := by
    change LocallyOfFiniteType (pullback.fst X.hom Z.hom ≫ X.hom); infer_instance
  haveI : IsReduced (X ⊗ Z).left := by
    have : GeometricallyIntegral X.hom := geometricallyIntegral_of_isAlgClosed X.hom
    have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
    have : LocallyOfFinitePresentation X.hom := inferInstance
    change IsReduced (Limits.pullback X.hom Z.hom); infer_instance

  have hM : ∀ τ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (X ⊗ Z).hom, Nonempty ((M.pullbackAlong τ).L ≅
      SheafOfModules.unit (Limits.pullback Y.hom (𝟙 (Spec (CommRingCat.of k)))).ringCatSheaf) := by
    intro τ
    let τ' : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X ⊗ Z := Over.homMk τ.1 τ.2
    have hA := stepA k X Y Z x₀ y₀ z₀ L hL h₁ h₂ h₃ (τ' ≫ fst X Z)
    have e : baseChangeSnd Y.hom τ ≫ σ.left =
        (Y ◁ (τ' ≫ snd X Z)).left ≫ (slice₁ X (Y ⊗ Z) (τ' ≫ fst X Z)).left := by
      change ((Y ◁ τ') ≫ σ).left = ((Y ◁ (τ' ≫ snd X Z)) ≫ slice₁ X (Y ⊗ Z) (τ' ≫ fst X Z)).left
      rw [whiskerLeft_swap]
    change Triv (baseChangeSnd Y.hom τ) ((Scheme.Modules.pullback σ.left).obj L)
    refine (triv_comp_iff _ _ _).mp ?_
    rw [triv_congr e]
    exact Triv.comp _ hA

  have hsee := RigidifiedLineBundle.nonempty_iso_unit_of_forall_pullbackAlong_point k Y.hom ε (X ⊗ Z).hom M hM

  have hT : Triv ((swap Y X Z).left ≫ σ.left) L :=
    (triv_comp_iff _ _ _).mpr (Triv.of_iso_unit _ hsee.some)
  have hσ : (swap Y X Z).left ≫ σ.left = 𝟙 _ := by
    change (swap Y X Z ≫ swap X Y Z).left = _
    rw [swap_swap]; rfl
  rw [triv_congr hσ] at hT
  exact (triv_id_iff L).mp hT

end Main

end P2mCubeAssembly

end
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] (X Y Z : Over (Spec (CommRingCat.of k)))
    [IsProper X.hom] [IsIntegral X.left] [IsProper Y.hom] [IsIntegral Y.left]
    [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsIntegral Z.left]
    (x₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X) (y₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Y)
    (z₀ : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Z)
    (L : (X ⊗ Y ⊗ Z).left.Modules) (hL : Scheme.Modules.IsInvertible L)
    (h₁ : Nonempty ((Scheme.Modules.pullback
      (lift (toUnit (Y ⊗ Z) ≫ x₀) (𝟙 (Y ⊗ Z)) : Y ⊗ Z ⟶ X ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _))
    (h₂ : Nonempty ((Scheme.Modules.pullback
      (lift (fst X Z) (lift (toUnit (X ⊗ Z) ≫ y₀) (snd X Z)) : X ⊗ Z ⟶ X ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _))
    (h₃ : Nonempty ((Scheme.Modules.pullback
      (lift (fst X Y) (lift (snd X Y) (toUnit (X ⊗ Y) ≫ z₀)) : X ⊗ Y ⟶ X ⊗ Y ⊗ Z).left).obj L ≅ 𝟙_ _)) :
    Nonempty (L ≅ 𝟙_ _) :=
  P2mCubeAssembly.main k X Y Z x₀ y₀ z₀ L hL h₁ h₂ h₃
