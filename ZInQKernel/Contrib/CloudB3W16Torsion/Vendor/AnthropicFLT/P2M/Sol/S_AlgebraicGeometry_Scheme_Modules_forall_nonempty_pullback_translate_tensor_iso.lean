/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_forall_nonempty_pullback_translate_tensor_iso. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_forall_nonempty_pullback_translate_tensor_iso

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory

open scoped CategoryTheory.MonObj

noncomputable section

namespace P2mSquare

section Skel

variable {C : Type*} [Category C] [MonoidalCategory C]

theorem cls_tensor (A B : C) : toSkeleton (A ⊗ B) = toSkeleton A * toSkeleton B :=
  Skeleton.toSkeleton_tensorObj A B

theorem cls_unit : toSkeleton (𝟙_ C) = (1 : Skeleton C) := Skeleton.one_eq.symm

theorem cls_congr {A B : C} (e : A ≅ B) : toSkeleton A = toSkeleton B :=
  toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩

theorem cls_of_nonempty {A B : C} (e : Nonempty (A ≅ B)) : toSkeleton A = toSkeleton B :=
  toSkeleton_eq_toSkeleton_iff.mpr e

end Skel

section Pull

variable {S T V : Scheme.{u}}

noncomputable abbrev pcls (φ : S ⟶ T) (A : T.Modules) : Skeleton S.Modules :=
  toSkeleton ((Scheme.Modules.pullback φ).obj A)

theorem pcls_tensor (φ : S ⟶ T) (A B : T.Modules) :
    pcls φ (A ⊗ B) = pcls φ A * pcls φ B := by
  rw [pcls, cls_congr (Scheme.Modules.pullbackTensorObjIso φ A B), cls_tensor]

theorem pcls_unit (φ : S ⟶ T) : pcls φ (𝟙_ T.Modules) = 1 := by
  rw [pcls, cls_congr (Scheme.Modules.pullbackTensorUnitObjIso φ), cls_unit]

theorem pcls_comp (φ : S ⟶ T) (ψ : T ⟶ V) (A : V.Modules) :
    pcls φ ((Scheme.Modules.pullback ψ).obj A) = pcls (φ ≫ ψ) A :=
  cls_congr ((Scheme.Modules.pullbackComp φ ψ).app A)

theorem pcls_id (A : T.Modules) : pcls (𝟙 T) A = toSkeleton A :=
  cls_congr ((Scheme.Modules.pullbackId T).app A)

theorem pcls_congr_hom {φ ψ : S ⟶ T} (h : φ = ψ) (A : T.Modules) : pcls φ A = pcls ψ A := by
  subst h; rfl

theorem pcls_congr_obj (φ : S ⟶ T) {A B : T.Modules} (h : toSkeleton A = toSkeleton B) :
    pcls φ A = pcls φ B :=
  cls_congr ((Scheme.Modules.pullback φ).mapIso (Skeleton.isoOfEq h))

theorem pcls_eq_one_of_cls_eq_one (φ : S ⟶ T) {A : T.Modules} (h : toSkeleton A = 1) :
    pcls φ A = 1 := by
  rw [pcls_congr_obj φ (h.trans cls_unit.symm), pcls_unit]

end Pull

section Main

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)] (L : X.Modules)

noncomputable abbrev Λ {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ Over.mk t) : Skeleton T.left.Modules :=
  pcls g.left L

theorem Λ_const (hL : Scheme.Modules.IsInvertible L) (T : Over (Spec (CommRingCat.of k)))
    (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    Λ k t L (toUnit T ≫ x) = 1 := by
  rw [Λ, Over.comp_left, ← pcls_comp]
  apply pcls_eq_one_of_cls_eq_one
  have htriv := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k
    ((Scheme.Modules.pullback x.left).obj L) (hL.pullback _)
  exact (cls_of_nonempty htriv).trans cls_unit

theorem Λ_id : Λ k t L (𝟙 (Over.mk t)) = toSkeleton L := by
  rw [Λ, Over.id_left]
  exact pcls_id L

theorem main (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (hL : Scheme.Modules.IsInvertible L)
    (x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    Nonempty (
      (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)).left).obj L ⊗
      (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)).left).obj L ≅
      (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (x * y))).left).obj L ⊗
      L) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  have hcube := Scheme.Modules.nonempty_pullback_mul_mul_tensor_iso k t hsm hpr hgc L hL
    (𝟙 (Over.mk t)) (toUnit (Over.mk t) ≫ x) (toUnit (Over.mk t) ≫ y)
  have e := cls_of_nonempty hcube
  simp only [cls_tensor] at e
  change Λ k t L _ * (Λ k t L _ * (Λ k t L _ * Λ k t L _)) = Λ k t L _ * (Λ k t L _ * Λ k t L _) at e
  rw [Λ_id, Λ_const k t L hL, Λ_const k t L hL, ← MonObj.comp_mul, Λ_const k t L hL, mul_one, mul_one, mul_one,
    mul_assoc (𝟙 (Over.mk t)), ← MonObj.comp_mul] at e
  rw [cls_tensor, cls_tensor]
  exact e.symm

end Main

end P2mSquare

end

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (x y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t) :
    Nonempty (
      (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ x)).left).obj L ⊗
      (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ y)).left).obj L ≅
      (Scheme.Modules.pullback (𝟙 (Over.mk t) * (CartesianMonoidalCategory.toUnit (Over.mk t) ≫ (x * y))).left).obj L ⊗
      L) :=
  P2mSquare.main k t L hsm hpr hgc hL x y
