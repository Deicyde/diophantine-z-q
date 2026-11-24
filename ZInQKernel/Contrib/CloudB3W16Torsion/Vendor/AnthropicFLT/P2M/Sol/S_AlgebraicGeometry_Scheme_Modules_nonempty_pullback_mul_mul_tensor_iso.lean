/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_iso_tensorUnit_of_pullback_three_slices
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isIntegral_of_smooth_of_geometricallyConnected
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_pullback_dual
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory

open scoped CategoryTheory.MonObj

namespace P2mCubeRed

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
  rw [pcls, cls_congr (Scheme.Modules.pullbackTensorObjIsoFLT φ A B), cls_tensor]

theorem pcls_unit (φ : S ⟶ T) : pcls φ (𝟙_ T.Modules) = 1 := by
  rw [pcls, cls_congr (Scheme.Modules.pullbackTensorUnitObjIso φ), cls_unit]

theorem pcls_comp (φ : S ⟶ T) (ψ : T ⟶ V) (A : V.Modules) :
    pcls φ ((Scheme.Modules.pullback ψ).obj A) = pcls (φ ≫ ψ) A :=
  cls_congr ((Scheme.Modules.pullbackComp φ ψ).app A)

theorem pcls_congr_hom {φ ψ : S ⟶ T} (h : φ = ψ) (A : T.Modules) : pcls φ A = pcls ψ A := by
  subst h; rfl

theorem pcls_congr_obj (φ : S ⟶ T) {A B : T.Modules} (h : toSkeleton A = toSkeleton B) :
    pcls φ A = pcls φ B :=
  cls_congr ((Scheme.Modules.pullback φ).mapIso (Skeleton.isoOfEq h))

theorem pcls_eq_one_of_cls_eq_one (φ : S ⟶ T) {A : T.Modules} (h : toSkeleton A = 1) :
    pcls φ A = 1 := by
  rw [pcls_congr_obj φ (h.trans cls_unit.symm), pcls_unit]

theorem cls_mul_cls_dual {A : T.Modules} (hA : Scheme.Modules.IsInvertible A) :
    toSkeleton A * toSkeleton (Scheme.Modules.fltDual A) = 1 := by
  rw [← cls_tensor, cls_of_nonempty hA.dual.2, cls_unit]

theorem pcls_dual (φ : S ⟶ T) {A : T.Modules} (hA : Scheme.Modules.IsInvertible A) :
    pcls φ (Scheme.Modules.fltDual A) =
      toSkeleton (Scheme.Modules.fltDual ((Scheme.Modules.pullback φ).obj A)) :=
  cls_of_nonempty (hA.pullback_dual φ)

end Pull

section Main

variable (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)] (L : X.Modules)

abbrev A : Over (Spec (CommRingCat.of k)) := Over.mk t

noncomputable abbrev P {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ Over.mk t) : T.left.Modules :=
  (Scheme.Modules.pullback g.left).obj L

noncomputable abbrev Λ {T : Over (Spec (CommRingCat.of k))} (g : T ⟶ Over.mk t) : Skeleton T.left.Modules :=
  pcls g.left L

theorem Λ_comp {T T' : Over (Spec (CommRingCat.of k))} (σ : T' ⟶ T) (g : T ⟶ Over.mk t) :
    pcls σ.left (P k t L g) = Λ k t L (σ ≫ g) := by
  rw [Λ, Over.comp_left]; exact pcls_comp _ _ _

theorem Λ_one (hL : Scheme.Modules.IsInvertible L) (T : Over (Spec (CommRingCat.of k))) :
    Λ k t L (1 : T ⟶ Over.mk t) = 1 := by
  have h1 : (1 : T ⟶ Over.mk t).left = T.hom ≫ (η : 𝟙_ _ ⟶ Over.mk t).left := by
    rw [Hom.one_def, Over.comp_left]; rfl
  rw [Λ, pcls_congr_hom h1, ← pcls_comp]
  apply pcls_eq_one_of_cls_eq_one
  have htriv := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k
    ((Scheme.Modules.pullback (η : 𝟙_ _ ⟶ Over.mk t).left).obj L) (hL.pullback _)
  exact (cls_of_nonempty htriv).trans cls_unit

abbrev A3 : Over (Spec (CommRingCat.of k)) := Over.mk t ⊗ (Over.mk t ⊗ Over.mk t)

abbrev p₁ : A3 k t ⟶ Over.mk t := fst _ _
abbrev p₂ : A3 k t ⟶ Over.mk t := snd _ _ ≫ fst _ _
abbrev p₃ : A3 k t ⟶ Over.mk t := snd _ _ ≫ snd _ _

noncomputable abbrev M₁ : (A3 k t).left.Modules :=
  P k t L (p₁ k t * p₂ k t * p₃ k t) ⊗ (P k t L (p₁ k t) ⊗ (P k t L (p₂ k t) ⊗ P k t L (p₃ k t)))

noncomputable abbrev M₂ : (A3 k t).left.Modules :=
  P k t L (p₁ k t * p₂ k t) ⊗ (P k t L (p₁ k t * p₃ k t) ⊗ P k t L (p₂ k t * p₃ k t))

theorem isInvertible_M₁ (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible (M₁ k t L) :=
  (hL.pullback _).tensor ((hL.pullback _).tensor ((hL.pullback _).tensor (hL.pullback _)))

theorem isInvertible_M₂ (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible (M₂ k t L) :=
  (hL.pullback _).tensor ((hL.pullback _).tensor (hL.pullback _))

theorem pcls_M₁ {T : Over (Spec (CommRingCat.of k))} (σ : T ⟶ A3 k t) (a b c : T ⟶ Over.mk t)
    (ha : σ ≫ p₁ k t = a) (hb : σ ≫ p₂ k t = b) (hc : σ ≫ p₃ k t = c) :
    pcls σ.left (M₁ k t L) =
      Λ k t L (a * b * c) * (Λ k t L a * (Λ k t L b * Λ k t L c)) := by
  rw [M₁, pcls_tensor, pcls_tensor, pcls_tensor, Λ_comp, Λ_comp, Λ_comp, Λ_comp,
    MonObj.comp_mul, MonObj.comp_mul, ha, hb, hc]

theorem pcls_M₂ {T : Over (Spec (CommRingCat.of k))} (σ : T ⟶ A3 k t) (a b c : T ⟶ Over.mk t)
    (ha : σ ≫ p₁ k t = a) (hb : σ ≫ p₂ k t = b) (hc : σ ≫ p₃ k t = c) :
    pcls σ.left (M₂ k t L) =
      Λ k t L (a * b) * (Λ k t L (a * c) * Λ k t L (b * c)) := by
  rw [M₂, pcls_tensor, pcls_tensor, Λ_comp, Λ_comp, Λ_comp,
    MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_mul, ha, hb, hc]

abbrev q₁ : Over.mk t ⊗ Over.mk t ⟶ Over.mk t := fst _ _
abbrev q₂ : Over.mk t ⊗ Over.mk t ⟶ Over.mk t := snd _ _

abbrev σ₁ : Over.mk t ⊗ Over.mk t ⟶ A3 k t :=
  lift (toUnit (Over.mk t ⊗ Over.mk t) ≫ (1 : 𝟙_ _ ⟶ Over.mk t)) (𝟙 (Over.mk t ⊗ Over.mk t))
abbrev σ₂ : Over.mk t ⊗ Over.mk t ⟶ A3 k t :=
  lift (fst (Over.mk t) (Over.mk t))
    (lift (toUnit (Over.mk t ⊗ Over.mk t) ≫ (1 : 𝟙_ _ ⟶ Over.mk t)) (snd (Over.mk t) (Over.mk t)))
abbrev σ₃ : Over.mk t ⊗ Over.mk t ⟶ A3 k t :=
  lift (fst (Over.mk t) (Over.mk t))
    (lift (snd (Over.mk t) (Over.mk t)) (toUnit (Over.mk t ⊗ Over.mk t) ≫ (1 : 𝟙_ _ ⟶ Over.mk t)))

theorem σ₁_p₁ : σ₁ k t ≫ p₁ k t = 1 := by
  rw [lift_fst, MonObj.comp_one]
theorem σ₁_p₂ : σ₁ k t ≫ p₂ k t = q₁ k t := by
  rw [lift_snd_assoc, Category.id_comp]
theorem σ₁_p₃ : σ₁ k t ≫ p₃ k t = q₂ k t := by
  rw [lift_snd_assoc, Category.id_comp]
theorem σ₂_p₁ : σ₂ k t ≫ p₁ k t = q₁ k t := by
  rw [lift_fst]
theorem σ₂_p₂ : σ₂ k t ≫ p₂ k t = 1 := by
  rw [lift_snd_assoc, lift_fst, MonObj.comp_one]
theorem σ₂_p₃ : σ₂ k t ≫ p₃ k t = q₂ k t := by
  rw [lift_snd_assoc, lift_snd]
theorem σ₃_p₁ : σ₃ k t ≫ p₁ k t = q₁ k t := by
  rw [lift_fst]
theorem σ₃_p₂ : σ₃ k t ≫ p₂ k t = q₂ k t := by
  rw [lift_snd_assoc, lift_fst]
theorem σ₃_p₃ : σ₃ k t ≫ p₃ k t = 1 := by
  rw [lift_snd_assoc, lift_snd, MonObj.comp_one]

theorem pcls_σ₁ (hL : Scheme.Modules.IsInvertible L) :
    pcls (σ₁ k t).left (M₁ k t L) =
      pcls (σ₁ k t).left (M₂ k t L) := by
  rw [pcls_M₁ k t L (σ₁ k t) 1 (q₁ k t) (q₂ k t) (σ₁_p₁ k t) (σ₁_p₂ k t) (σ₁_p₃ k t),
    pcls_M₂ k t L (σ₁ k t) 1 (q₁ k t) (q₂ k t) (σ₁_p₁ k t) (σ₁_p₂ k t) (σ₁_p₃ k t),
    one_mul, one_mul, Λ_one k t L hL, one_mul]
  ac_rfl

theorem pcls_σ₂ (hL : Scheme.Modules.IsInvertible L) :
    pcls (σ₂ k t).left (M₁ k t L) =
      pcls (σ₂ k t).left (M₂ k t L) := by
  rw [pcls_M₁ k t L (σ₂ k t) (q₁ k t) 1 (q₂ k t) (σ₂_p₁ k t) (σ₂_p₂ k t) (σ₂_p₃ k t),
    pcls_M₂ k t L (σ₂ k t) (q₁ k t) 1 (q₂ k t) (σ₂_p₁ k t) (σ₂_p₂ k t) (σ₂_p₃ k t),
    mul_one, one_mul, Λ_one k t L hL, one_mul]
  ac_rfl

theorem pcls_σ₃ (hL : Scheme.Modules.IsInvertible L) :
    pcls (σ₃ k t).left (M₁ k t L) =
      pcls (σ₃ k t).left (M₂ k t L) := by
  rw [pcls_M₁ k t L (σ₃ k t) (q₁ k t) (q₂ k t) 1 (σ₃_p₁ k t) (σ₃_p₂ k t) (σ₃_p₃ k t),
    pcls_M₂ k t L (σ₃ k t) (q₁ k t) (q₂ k t) 1 (σ₃_p₁ k t) (σ₃_p₂ k t) (σ₃_p₃ k t),
    mul_one, mul_one, mul_one, Λ_one k t L hL, mul_one]

noncomputable abbrev N : (A3 k t).left.Modules :=
  M₁ k t L ⊗ Scheme.Modules.fltDual (M₂ k t L)

theorem isInvertible_N (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible (N k t L) :=
  (isInvertible_M₁ k t L hL).tensor (isInvertible_M₂ k t L hL).dual.1

theorem slice_trivial (hL : Scheme.Modules.IsInvertible L) {T : Over (Spec (CommRingCat.of k))}
    (σ : T ⟶ A3 k t)
    (h : pcls σ.left (M₁ k t L) = pcls σ.left (M₂ k t L)) :
    Nonempty ((Scheme.Modules.pullback σ.left).obj (N k t L) ≅ 𝟙_ _) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  rw [← pcls, N, pcls_tensor, h, pcls_dual _ (isInvertible_M₂ k t L hL), pcls,
    cls_mul_cls_dual ((isInvertible_M₂ k t L hL).pullback _), cls_unit]

theorem cls_M₁_eq_cls_M₂ (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (hL : Scheme.Modules.IsInvertible L) :
    toSkeleton (M₁ k t L) = toSkeleton (M₂ k t L) := by
  haveI : IsProper (Over.mk t : Over (Spec (CommRingCat.of k))).hom := hpr
  haveI : IsIntegral (Over.mk t : Over (Spec (CommRingCat.of k))).left :=
    AlgebraicGeometry.isIntegral_of_smooth_of_geometricallyConnected k t hsm hgc
      (η : 𝟙_ _ ⟶ Over.mk t).left (Over.w (η : 𝟙_ _ ⟶ Over.mk t))
  have hN := Scheme.Modules.nonempty_iso_tensorUnit_of_pullback_three_slices k
    (Over.mk t) (Over.mk t) (Over.mk t) 1 1 1 (N k t L) (isInvertible_N k t L hL)
    (slice_trivial k t L hL (σ₁ k t) (pcls_σ₁ k t L hL)) (slice_trivial k t L hL (σ₂ k t) (pcls_σ₂ k t L hL))
    (slice_trivial k t L hL (σ₃ k t) (pcls_σ₃ k t L hL))
  have h1 : toSkeleton (N k t L) = 1 := by rw [cls_of_nonempty hN, cls_unit]
  rw [N, cls_tensor] at h1

  have h2 := cls_mul_cls_dual (isInvertible_M₂ k t L hL)
  calc toSkeleton (M₁ k t L)
      = toSkeleton (M₁ k t L) * (toSkeleton (M₂ k t L) * toSkeleton (Scheme.Modules.fltDual (M₂ k t L))) := by
        rw [h2, mul_one]
    _ = toSkeleton (M₁ k t L) * toSkeleton (Scheme.Modules.fltDual (M₂ k t L)) * toSkeleton (M₂ k t L) := by
        rw [mul_assoc, mul_comm (toSkeleton (M₂ k t L))]
    _ = toSkeleton (M₂ k t L) := by rw [h1, one_mul]

theorem main (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (hL : Scheme.Modules.IsInvertible L)
    {Y : Over (Spec (CommRingCat.of k))} (f g h : Y ⟶ Over.mk t) :
    Nonempty (
      (Scheme.Modules.pullback (f * g * h).left).obj L ⊗ (Scheme.Modules.pullback f.left).obj L ⊗
          (Scheme.Modules.pullback g.left).obj L ⊗ (Scheme.Modules.pullback h.left).obj L ≅
        (Scheme.Modules.pullback (f * g).left).obj L ⊗ (Scheme.Modules.pullback (f * h).left).obj L ⊗
          (Scheme.Modules.pullback (g * h).left).obj L) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  let φ : Y ⟶ A3 k t := lift f (lift g h)
  have ha : φ ≫ p₁ k t = f := lift_fst _ _
  have hb : φ ≫ p₂ k t = g := by rw [lift_snd_assoc, lift_fst]
  have hc : φ ≫ p₃ k t = h := by rw [lift_snd_assoc, lift_snd]
  have e := pcls_congr_obj φ.left (cls_M₁_eq_cls_M₂ k t L hsm hpr hgc hL)
  rw [pcls_M₁ k t L φ f g h ha hb hc, pcls_M₂ k t L φ f g h ha hb hc] at e
  simpa only [cls_tensor] using e

end Main

end P2mCubeRed

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    {Y : Over (Spec (CommRingCat.of k))} (f g h : Y ⟶ Over.mk t) :
    Nonempty (
      (Scheme.Modules.pullback (f * g * h).left).obj L ⊗ (Scheme.Modules.pullback f.left).obj L ⊗
          (Scheme.Modules.pullback g.left).obj L ⊗ (Scheme.Modules.pullback h.left).obj L ≅
        (Scheme.Modules.pullback (f * g).left).obj L ⊗ (Scheme.Modules.pullback (f * h).left).obj L ⊗
          (Scheme.Modules.pullback (g * h).left).obj L) :=
  P2mCubeRed.main k t L hsm hpr hgc hL f g h

end
