/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_diffQExp_x1FunctionFieldBar_injective (git blob c6eb035657167671ed1db8162ce6fd39d53fa441, sha256 ac37c1b53396c5ab0f2d3bf33944d1794a49b84357c702de60a27757d41786bb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_HeckeDifferential
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_KaehlerDifferential_exists_unique_smul_D_of_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_diffQExp_x1FunctionFieldBar_injective

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

theorem solution (M : ℕ) [NeZero M] :
    Function.Injective ⇑(ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M)) := by

  obtain ⟨x, hxT, hxfd⟩ : ∃ x : ↥(ModularCurve.x1FunctionFieldBar M), Transcendental (AlgebraicClosure ℚ) x ∧
      FiniteDimensional ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(ModularCurve.x1FunctionFieldBar M)))
        ↥(ModularCurve.x1FunctionFieldBar M) :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange
      (AlgebraicClosure ℚ) (CongruenceSubgroup.Gamma1 M) (by rw [CongruenceSubgroup.Gamma1_mem]; simp [ModularGroup.T])
  haveI : FiniteDimensional
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(ModularCurve.x1FunctionFieldBar M)))
      ↥(ModularCurve.x1FunctionFieldBar M) := hxfd
  haveI : Algebra.IsAlgebraic
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(ModularCurve.x1FunctionFieldBar M)))
      ↥(ModularCurve.x1FunctionFieldBar M) := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable
      ↥(IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(ModularCurve.x1FunctionFieldBar M)))
      ↥(ModularCurve.x1FunctionFieldBar M) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField

  rw [injective_iff_map_eq_zero]
  intro ω hω
  obtain ⟨c, hc, -⟩ := KaehlerDifferential.exists_unique_smul_D_of_transcendental (AlgebraicClosure ℚ) x hxT ω
  rw [hc, ModularCurve.diffQExp_smul_D] at hω
  rcases mul_eq_zero.mp hω with hc0 | hq0
  · have hc00 : c = 0 := by exact_mod_cast hc0
    rw [hc, hc00, zero_smul]
  ·
    exfalso
    apply hxT
    have hcoeff : ∀ n : ℤ, n ≠ 0 → (x : LaurentSeries (AlgebraicClosure ℚ)).coeff n = 0 := by
      intro n hn
      have h := congrArg (fun y : LaurentSeries (AlgebraicClosure ℚ) => y.coeff n) hq0
      simp only [HahnSeries.coeff_zero] at h
      change ((n : AlgebraicClosure ℚ)) * (x : LaurentSeries (AlgebraicClosure ℚ)).coeff n = 0 at h
      exact (mul_eq_zero.mp h).resolve_left (Int.cast_ne_zero.mpr hn)
    set a : AlgebraicClosure ℚ := (x : LaurentSeries (AlgebraicClosure ℚ)).coeff 0 with ha
    have hx : (x : LaurentSeries (AlgebraicClosure ℚ)) =
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a := by
      rw [ModularCurve.algebraMap_laurentSeries_eq_single]
      ext n
      by_cases hn : n = 0
      · subst hn; simp [ha]
      · rw [hcoeff n hn, HahnSeries.coeff_single_of_ne hn]
    have hx' : x = algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) a := by
      apply Subtype.ext
      rw [hx, IsScalarTower.algebraMap_apply (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)
        (LaurentSeries (AlgebraicClosure ℚ)) a]
      rfl
    rw [hx']
    exact isAlgebraic_algebraMap _
