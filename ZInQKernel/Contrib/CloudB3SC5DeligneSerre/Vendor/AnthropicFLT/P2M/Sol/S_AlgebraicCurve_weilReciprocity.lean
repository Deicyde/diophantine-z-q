/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_weilReciprocity (git blob 92a00c8d6bd88548df0c1561957382e10d1675bf, sha256 176098d3873dab7441142bb3d28364cdbb8f60b29a8f9200fb6049d4a8769b0d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RationalFunctionField_weilReciprocity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_weilReciprocity_algebraMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_FunctionField_finite_of_ratFuncAlgHom
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_FunctionField_exists_ratFuncAlgHom_apply_X_eq
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RationalFunctionField_deg_eq_one_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_isRational_iff_deg_eq_one
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RationalFunctionField_hasPrincipalDivisors
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_ord_algebraMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace AlgebraicCurve
end AlgebraicCurve
namespace P2MW.S_AlgebraicCurve_weilReciprocity.AlgebraicCurve
end P2MW.S_AlgebraicCurve_weilReciprocity.AlgebraicCurve

namespace P2MW.S_AlgebraicCurve_weilReciprocity

set_option autoImplicit false

open _root_.AlgebraicCurve
open _root_.P2MW.S_AlgebraicCurve_weilReciprocity.AlgebraicCurve

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Place.IsRational Place.evalAt Divisor.evalFun_def Divisor.evalFun_zero WeilReciprocity Place Divisor Divisor.degree HasPrincipalDivisors HasPrincipalDivisors.exists_divisor RationalFunctionField.weilReciprocity weilReciprocity_algebraMap FunctionField.finite_of_ratFuncAlgHom FunctionField.exists_ratFuncAlgHom_apply_X_eq Place.isRational_of_isAlgClosed RationalFunctionField.deg_eq_one_of_isAlgClosed Place.isRational_iff_deg_eq_one RationalFunctionField.hasPrincipalDivisors Place.evalAt_algebraMap Place.ord_algebraMap)
namespace WeilReciprocityAnchor
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem finsupp_prod_zpow_const {c : K} (hc : c ≠ 0) (D : Divisor K F) :
    (D.prod fun _ n => c ^ n) = c ^ (D.sum fun _ n => n) := by
  classical
  unfold Finsupp.prod Finsupp.sum
  induction D.support using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hc, ih]

theorem degree_eq_sum_of_rational (D : Divisor K F)
    (hrat : ∀ v ∈ D.support, Place.IsRational v) :
    Divisor.degree D = D.sum fun _ n => n := by
  unfold Divisor.degree
  rw [Finsupp.liftAddHom_apply]
  refine Finsupp.sum_congr fun v hv => ?_
  rw [AddMonoidHom.mulRight_apply, (AlgebraicCurve.Place.isRational_iff_deg_eq_one v).1 (hrat v hv),
    Nat.cast_one, mul_one]

end AlgebraicCurve.WeilReciprocityAnchor

open AlgebraicCurve.WeilReciprocityAnchor in
theorem solution (K F : Type*) [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] [HasPrincipalDivisors K F] : WeilReciprocity K F := by
  classical
  intro f g Df Dg hf hg hDf hDg hdisj hratf hratg
  by_cases hconst : g ∈ Set.range (algebraMap K F)
  ·
    obtain ⟨c, rfl⟩ := hconst
    have hc : c ≠ 0 := fun h => hg (by rw [h, map_zero])
    have hDg0 : Dg = 0 := by
      ext v
      rw [hDg v, AlgebraicCurve.Place.ord_algebraMap, Finsupp.coe_zero, Pi.zero_apply]

    obtain ⟨D', hD', hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
    have hDfD' : Df = D' := by
      ext v; rw [hDf v, hD' v]
    have hsum : (Df.sum fun _ n => n) = 0 := by
      rw [← degree_eq_sum_of_rational Df hratf, hDfD', hdeg]
    rw [hDg0, Divisor.evalFun_zero, Divisor.evalFun_def]
    rw [show (∏ v ∈ Df.support, Place.evalAt v (algebraMap K F c) ^ Df v)
        = Df.prod fun _ n => c ^ n from
      Finset.prod_congr rfl fun v _ => by rw [AlgebraicCurve.Place.evalAt_algebraMap]]
    rw [finsupp_prod_zpow_const hc, hsum, zpow_zero]
  ·
    obtain ⟨φ, hφ⟩ := AlgebraicCurve.FunctionField.exists_ratFuncAlgHom_apply_X_eq hconst

    have finφ : @Module.Finite (RatFunc K) F _ _ (φ.toRingHom.toAlgebra).toModule :=
      AlgebraicCurve.FunctionField.finite_of_ratFuncAlgHom φ

    let algφ : Algebra (RatFunc K) F := φ.toRingHom.toAlgebra
    have stφ : @IsScalarTower K (RatFunc K) F _ algφ.toSMul _ :=
      @IsScalarTower.of_algebraMap_eq K (RatFunc K) F _ _ _ _ algφ _ fun x => (φ.commutes x).symm
    haveI : CharZero (RatFunc K) :=
      charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
    have algc : @Algebra.IsAlgebraic (RatFunc K) F _ _ algφ :=
      @Algebra.IsAlgebraic.of_finite (RatFunc K) F _ _ _ algφ finφ
    have sepφ : @Algebra.IsSeparable (RatFunc K) F _ _ algφ :=
      @Algebra.IsAlgebraic.isSeparable_of_perfectField (RatFunc K) F _ _ algφ algc _
    haveI : HasPrincipalDivisors K (RatFunc K) :=
      AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors K
    have hXg : @algebraMap (RatFunc K) F _ _ algφ RatFunc.X = g := hφ
    have hratF : ∀ v : Place K (RatFunc K), v.IsRational := fun v =>
      (AlgebraicCurve.Place.isRational_iff_deg_eq_one v).2
        (AlgebraicCurve.RationalFunctionField.deg_eq_one_of_isAlgClosed K v)
    have hratAll : ∀ w : Place K F, w.IsRational := fun w =>
      @AlgebraicCurve.Place.isRational_of_isAlgClosed K F _ _ _ _ algφ stφ finφ w
    have key := @AlgebraicCurve.weilReciprocity_algebraMap K (RatFunc K) F _ _ _ _ _ algφ stφ finφ sepφ
      _ _ _ (AlgebraicCurve.RationalFunctionField.weilReciprocity K) f RatFunc.X hf RatFunc.X_ne_zero
      Df Dg hDf (fun w => by rw [hDg w, ← hXg]) (fun w => by rw [← hXg] at hdisj; exact hdisj w) hratf hratF
      (fun v _ w _ => hratAll w)
    rw [hXg] at key
    exact key
