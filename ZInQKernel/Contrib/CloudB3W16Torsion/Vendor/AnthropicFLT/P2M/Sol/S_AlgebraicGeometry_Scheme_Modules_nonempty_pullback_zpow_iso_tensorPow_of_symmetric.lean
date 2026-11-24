/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_zpow_iso_tensorPow_of_symmetric. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_mul_mul_tensor_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_tensor_inverse
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_zpow_iso_tensorPow_of_symmetric

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

open scoped CategoryTheory.MonObj

namespace P2mMumfordSymN

section Skel

variable {C : Type*} [Category C] [MonoidalCategory C]

theorem cls_tensor (A B : C) : toSkeleton (A ⊗ B) = toSkeleton A * toSkeleton B :=
  Skeleton.toSkeleton_tensorObj A B

theorem cls_unit : toSkeleton (𝟙_ C) = (1 : Skeleton C) := Skeleton.one_eq.symm

end Skel

section Modules

variable {Z : Scheme.{u}}

theorem cls_tensorPow (N : Z.Modules) (n : ℕ) :
    toSkeleton (N.tensorPowFLT n) = toSkeleton N ^ n := by
  induction n with
  | zero => rw [Scheme.Modules.tensorPow_zeroFLT, cls_unit, pow_zero]
  | succ n ih => rw [Scheme.Modules.tensorPow_succFLT, cls_tensor, ih, pow_succ]

theorem isUnit_toSkeleton {N : Z.Modules} (hN : Scheme.Modules.IsInvertible N) :
    IsUnit (toSkeleton N) := by
  obtain ⟨M, -, ⟨e⟩⟩ := hN.exists_tensor_inverse
  have h := toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩
  rw [cls_tensor, cls_unit] at h
  exact IsUnit.of_mul_eq_one _ h

end Modules

section Main

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} {t : X ⟶ Spec (CommRingCat.of k)}
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)] {L : X.Modules}

variable (t L) in

noncomputable def Λ (f : Over.mk t ⟶ Over.mk t) : Skeleton X.Modules :=
  toSkeleton ((Scheme.Modules.pullback f.left).obj L)

theorem cube (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (hL : Scheme.Modules.IsInvertible L) (f g h : Over.mk t ⟶ Over.mk t) :
    Λ t L (f * g * h) * (Λ t L f * (Λ t L g * Λ t L h)) =
      Λ t L (f * g) * (Λ t L (f * h) * Λ t L (g * h)) := by
  obtain ⟨e⟩ := Scheme.Modules.nonempty_pullback_mul_mul_tensor_iso k t hsm hpr hgc L hL f g h
  have := toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩
  simp only [cls_tensor] at this
  exact this

theorem isUnit_Λ (hL : Scheme.Modules.IsInvertible L) (f : Over.mk t ⟶ Over.mk t) : IsUnit (Λ t L f) :=
  isUnit_toSkeleton (hL.pullback f.left)

noncomputable def U (hL : Scheme.Modules.IsInvertible L) (f : Over.mk t ⟶ Over.mk t) :
    (Skeleton X.Modules)ˣ :=
  (isUnit_Λ hL f).unit

@[scoped simp] theorem U_val (hL : Scheme.Modules.IsInvertible L) (f : Over.mk t ⟶ Over.mk t) :
    (U hL f : Skeleton X.Modules) = Λ t L f :=
  rfl

theorem cubeU (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (hL : Scheme.Modules.IsInvertible L) (f g h : Over.mk t ⟶ Over.mk t) :
    U hL (f * g * h) * U hL f * U hL g * U hL h = U hL (f * g) * U hL (f * h) * U hL (g * h) := by
  ext
  simp only [Units.val_mul, U_val]
  have hc := cube hsm hpr hgc hL f g h
  simpa only [← mul_assoc] using hc

theorem U_one (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (hL : Scheme.Modules.IsInvertible L) : U hL (1 : Over.mk t ⟶ Over.mk t) = 1 := by
  have h := cubeU hsm hpr hgc hL (1 : Over.mk t ⟶ Over.mk t) 1 1
  simp only [mul_one] at h
  set e : Over.mk t ⟶ Over.mk t := 1
  have h' : U hL e * (U hL e * U hL e * U hL e) = 1 * (U hL e * U hL e * U hL e) := by
    rw [one_mul, ← mul_assoc, ← mul_assoc]; exact h
  exact mul_right_cancel h'

theorem U_id_val (hL : Scheme.Modules.IsInvertible L) :
    (U hL (𝟙 (Over.mk t)) : Skeleton X.Modules) = toSkeleton L :=
  toSkeleton_eq_toSkeleton_iff.mpr ⟨(Scheme.Modules.pullbackId X).app L⟩

theorem U_rec (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (hL : Scheme.Modules.IsInvertible L) (n : ℤ) :
    U hL ((𝟙 (Over.mk t)) ^ (n + 2)) * U hL ((𝟙 (Over.mk t)) ^ n) =
      U hL ((𝟙 (Over.mk t)) ^ (n + 1)) * U hL ((𝟙 (Over.mk t)) ^ (n + 1)) *
        U hL (𝟙 (Over.mk t)) * U hL (𝟙 (Over.mk t))⁻¹ := by
  have h := cubeU hsm hpr hgc hL ((𝟙 (Over.mk t)) ^ (n + 1)) (𝟙 (Over.mk t)) (𝟙 (Over.mk t))⁻¹
  rw [mul_inv_cancel_right, mul_inv_cancel, U_one hsm hpr hgc hL, mul_one, ← zpow_add_one, add_assoc,
    one_add_one_eq_two, ← zpow_sub_one, add_sub_cancel_right] at h
  exact h.symm

theorem U_zpow (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (hL : Scheme.Modules.IsInvertible L)
    (hsym : Nonempty ((Scheme.Modules.pullback ((𝟙 (Over.mk t))⁻¹).left).obj L ≅ L)) (n : ℤ) :
    U hL ((𝟙 (Over.mk t)) ^ n) = (isUnit_toSkeleton hL).unit ^ (n * n) := by
  set w : (Skeleton X.Modules)ˣ := (isUnit_toSkeleton hL).unit with hw

  have h1 : U hL (𝟙 (Over.mk t)) = w := Units.ext (U_id_val hL)
  have hm1 : U hL (𝟙 (Over.mk t))⁻¹ = w := Units.ext (toSkeleton_eq_toSkeleton_iff.mpr hsym)

  have hrec : ∀ m : ℤ, U hL ((𝟙 (Over.mk t)) ^ (m + 2)) * U hL ((𝟙 (Over.mk t)) ^ m) =
      U hL ((𝟙 (Over.mk t)) ^ (m + 1)) * U hL ((𝟙 (Over.mk t)) ^ (m + 1)) * w * w := by
    intro m
    have r := U_rec hsm hpr hgc hL m
    rw [h1, hm1] at r
    exact r

  have base0 : U hL ((𝟙 (Over.mk t)) ^ (0 : ℤ)) = w ^ ((0 : ℤ) * 0) := by
    rw [zpow_zero, mul_zero, zpow_zero]; exact U_one hsm hpr hgc hL
  have base1 : U hL ((𝟙 (Over.mk t)) ^ (1 : ℤ)) = w ^ ((1 : ℤ) * 1) := by
    rw [zpow_one, mul_one, zpow_one]; exact h1

  have up : ∀ m : ℤ, U hL ((𝟙 (Over.mk t)) ^ m) = w ^ (m * m) →
      U hL ((𝟙 (Over.mk t)) ^ (m + 1)) = w ^ ((m + 1) * (m + 1)) →
      U hL ((𝟙 (Over.mk t)) ^ (m + 2)) = w ^ ((m + 2) * (m + 2)) := by
    intro m e0 e1
    have r := hrec m
    rw [e0, e1] at r
    rw [eq_mul_inv_of_mul_eq r, ← zpow_add, ← zpow_add_one, ← zpow_add_one, ← zpow_sub]
    congr 1; ring

  have down : ∀ m : ℤ, U hL ((𝟙 (Over.mk t)) ^ (m + 1)) = w ^ ((m + 1) * (m + 1)) →
      U hL ((𝟙 (Over.mk t)) ^ (m + 2)) = w ^ ((m + 2) * (m + 2)) →
      U hL ((𝟙 (Over.mk t)) ^ m) = w ^ (m * m) := by
    intro m e1 e2
    have r := hrec m
    rw [e1, e2] at r
    rw [eq_inv_mul_of_mul_eq r, ← zpow_add, ← zpow_add_one, ← zpow_add_one, ← zpow_neg, ← zpow_add]
    congr 1; ring

  have hup : ∀ m : ℕ, U hL ((𝟙 (Over.mk t)) ^ (m : ℤ)) = w ^ ((m : ℤ) * m) ∧
      U hL ((𝟙 (Over.mk t)) ^ ((m : ℤ) + 1)) = w ^ (((m : ℤ) + 1) * ((m : ℤ) + 1)) := by
    intro m
    induction m with
    | zero => simp only [Nat.cast_zero, zero_add]; exact ⟨base0, base1⟩
    | succ m ih =>
      have e : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      have e' : ((m + 1 : ℕ) : ℤ) + 1 = (m : ℤ) + 2 := by push_cast; ring
      refine ⟨?_, ?_⟩
      · rw [e]; exact ih.2
      · rw [e']; exact up (m : ℤ) ih.1 ih.2

  have hdown : ∀ m : ℕ, U hL ((𝟙 (Over.mk t)) ^ (-(m : ℤ))) = w ^ ((-(m : ℤ)) * (-(m : ℤ))) ∧
      U hL ((𝟙 (Over.mk t)) ^ (-(m : ℤ) + 1)) = w ^ ((-(m : ℤ) + 1) * (-(m : ℤ) + 1)) := by
    intro m
    induction m with
    | zero => simp only [Nat.cast_zero, neg_zero, zero_add]; exact ⟨base0, base1⟩
    | succ m ih =>
      have e1 : (-((m + 1 : ℕ) : ℤ)) + 1 = -(m : ℤ) := by push_cast; ring
      have e2 : (-((m + 1 : ℕ) : ℤ)) + 2 = -(m : ℤ) + 1 := by push_cast; ring
      refine ⟨?_, ?_⟩
      · exact down _ (by rw [e1]; exact ih.1) (by rw [e2]; exact ih.2)
      · rw [e1]; exact ih.1
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · exact (hup m).1
  · exact (hdown m).1

theorem main (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (hL : Scheme.Modules.IsInvertible L)
    (hsym : Nonempty ((Scheme.Modules.pullback ((𝟙 (Over.mk t))⁻¹).left).obj L ≅ L)) (n : ℤ) :
    Nonempty ((Scheme.Modules.pullback ((𝟙 (Over.mk t)) ^ n).left).obj L ≅ L.tensorPowFLT (n * n).toNat) := by
  apply toSkeleton_eq_toSkeleton_iff.mp
  have h := congrArg Units.val (U_zpow hsm hpr hgc hL hsym n)
  rw [U_val, ← Int.toNat_of_nonneg (mul_self_nonneg n), zpow_natCast, Units.val_pow_eq_pow_val,
    IsUnit.unit_spec, ← cls_tensorPow] at h
  exact h

end Main

end P2mMumfordSymN

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [GrpObj (Over.mk t)] [IsCommMonObj (Over.mk t)]
    (hsm : Smooth t) (hpr : IsProper t) (hgc : GeometricallyConnected t)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hsym : Nonempty ((Scheme.Modules.pullback ((𝟙 (Over.mk t))⁻¹).left).obj L ≅ L)) (n : ℤ) :
    Nonempty ((Scheme.Modules.pullback ((𝟙 (Over.mk t)) ^ n).left).obj L ≅ L.tensorPowFLT (n * n).toNat) :=
  P2mMumfordSymN.main hsm hpr hgc hL hsym n
