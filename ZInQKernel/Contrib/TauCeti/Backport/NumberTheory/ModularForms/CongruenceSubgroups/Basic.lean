/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 4d91513e4d30, module
-- TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic), Apache-2.0: declarations added to
-- that module after commit 5a01f5fe, whose version is vendored as
-- `ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic
import ZInQKernel.Contrib.TauCeti.Data.ZMod.Divisibility

/-!
# `Γ₁(lcm a b) = Γ₁(a) ⊓ Γ₁(b)` and the `Γ₁(gcd a b)` factorisation (backport)
-/

public section

open Matrix Matrix.SpecialLinearGroup

open scoped MatrixGroups Pointwise

namespace CongruenceSubgroup

/-- **`Γ₁(lcm a b) = Γ₁(a) ⊓ Γ₁(b)`**: the three congruences cutting out `Γ₁` hold modulo
`lcm a b` exactly when they hold modulo both `a` and `b`. -/
theorem Gamma1_lcm_eq_inf (a b : ℕ) : Gamma1 (Nat.lcm a b) = Gamma1 a ⊓ Gamma1 b := by
  refine le_antisymm (le_inf (Gamma1_le_Gamma1_of_dvd (Nat.dvd_lcm_left a b))
    (Gamma1_le_Gamma1_of_dvd (Nat.dvd_lcm_right a b))) fun γ hγ ↦ ?_
  obtain ⟨ha, hb⟩ := Subgroup.mem_inf.mp hγ
  rw [Gamma1_mem] at ha hb ⊢
  refine ⟨?_, ?_, ?_⟩
  · simpa using ZMod.intCast_lcm_eq_of_eq_of_eq (y := 1) (by simpa using ha.1) (by simpa using hb.1)
  · simpa using ZMod.intCast_lcm_eq_of_eq_of_eq (y := 1) (by simpa using ha.2.1)
      (by simpa using hb.2.1)
  · simpa using ZMod.intCast_lcm_eq_of_eq_of_eq (y := 0) (by simpa using ha.2.2)
      (by simpa using hb.2.2)

/-- **Every matrix of `Γ₁(gcd a b)` is a product of one of `Γ₁(a)` and one of `Γ₁(b)`.** The
subgroup `Γ₁(a)` is not normal, so this product decomposition is stronger than the equality of
subgroups `Gamma1_gcd_eq_sup`; it is what identifies the cosets of `Γ₁(lcm a b)` in `Γ₁(a)` with
those of `Γ₁(b)` in `Γ₁(gcd a b)`. -/
theorem exists_mul_eq_of_mem_Gamma1_gcd {a b : ℕ} {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma1 (Nat.gcd a b)) : ∃ α ∈ Gamma1 a, ∃ β ∈ Gamma1 b, α * β = γ := by
  -- dividing `γ` on the left by `Tⁿ`, `n` its upper-right entry, lands in
  -- `Γ(gcd a b) = Γ(a) ⊔ Γ(b)`, where `Γ(a)` is normal; and `Tⁿ` lies in every `Γ₁`
  have hδ : ModularGroup.T ^ (-(γ 0 1)) * γ ∈ Gamma (Nat.gcd a b) := by
    obtain ⟨h00, h11, h10⟩ := (Gamma1_mem _ _).mp hγ
    rw [Gamma_mem]
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T_zpow, h00, h11, h10]
  have : (Gamma a).Normal := Gamma_normal a
  rw [Gamma_gcd_eq_sup, Subgroup.mem_sup_of_normal_left] at hδ
  obtain ⟨y, hy, z, hz, hyz⟩ := hδ
  refine ⟨ModularGroup.T ^ (γ 0 1) * y,
    mul_mem (T_zpow_mem_Gamma1 a _) (Gamma_le_Gamma1 a hy), z, Gamma_le_Gamma1 b hz, ?_⟩
  rw [mul_assoc, hyz, ← mul_assoc, ← _root_.zpow_add, add_neg_cancel, _root_.zpow_zero, one_mul]

end CongruenceSubgroup
