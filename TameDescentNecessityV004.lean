import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.NormNum

/-!
# The Frobenius conjugation in the tame-descent engine cannot be dropped

On the line `ℚ`, the finite group `{1, -1}` is normalized (indeed centralized) by
multiplication by `2`. Positive powers of `2` fix only `0`, so the rigidity
hypothesis "every `T ^ m`-fixed vector is `Q`-fixed" holds, yet `-1` acts
nontrivially. Here `T = 2` is not conjugate to any power `T ^ q` with `q ≥ 2`.
-/

noncomputable section
set_option autoImplicit false

namespace WildTameDescent

theorem rigidity_alone_insufficient :
    ∃ (Q : Subgroup (Module.End ℚ ℚ)ˣ) (T : (Module.End ℚ ℚ)ˣ),
      (Q : Set (Module.End ℚ ℚ)ˣ).Finite ∧
      T ∈ Subgroup.normalizer (Q : Set (Module.End ℚ ℚ)ˣ) ∧
      (∀ m : ℕ, 0 < m → ∀ v : ℚ, ((T : Module.End ℚ ℚ) ^ m) v = v →
        ∀ g ∈ Q, (g : Module.End ℚ ℚ) v = v) ∧
      ∃ g ∈ Q, ∃ v : ℚ, (g : Module.End ℚ ℚ) v ≠ v := by
  let u : (Module.End ℚ ℚ)ˣ := -1
  let c : (Module.End ℚ ℚ)ˣ :=
    Units.map (algebraMap ℚ (Module.End ℚ ℚ)).toMonoidHom (Units.mk0 (2 : ℚ) two_ne_zero)
  have hc : ∀ v : ℚ, (c : Module.End ℚ ℚ) v = 2 * v := by
    intro v
    change algebraMap ℚ (Module.End ℚ ℚ) 2 v = 2 * v
    rw [Module.algebraMap_end_apply, smul_eq_mul]
  have hcpow : ∀ (m : ℕ) (v : ℚ), ((c : Module.End ℚ ℚ) ^ m) v = 2 ^ m * v := by
    intro m
    induction m with
    | zero => intro v; simp
    | succ m ih =>
      intro v
      rw [pow_succ, Module.End.mul_apply, hc, ih, pow_succ, mul_assoc]
  have hcomm : ∀ g : (Module.End ℚ ℚ)ˣ, c * g * c⁻¹ = g := by
    intro g
    have hcg : c * g = g * c := by
      apply Units.ext
      apply LinearMap.ext
      intro v
      change (c : Module.End ℚ ℚ) ((g : Module.End ℚ ℚ) v) =
        (g : Module.End ℚ ℚ) ((c : Module.End ℚ ℚ) v)
      rw [hc, hc, ← smul_eq_mul (2 : ℚ) v, map_smul, smul_eq_mul]
    rw [hcg, mul_inv_cancel_right]
  have hu2 : u * u = 1 := by simp [u]
  have hsub : (Subgroup.zpowers u : Set (Module.End ℚ ℚ)ˣ) ⊆ {1, u} := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, hu2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hu2, one_zpow, one_mul, zpow_one]
      exact Set.mem_singleton u
  refine ⟨Subgroup.zpowers u, c, (Set.toFinite _).subset hsub, ?_, ?_, ⟨u, Subgroup.mem_zpowers u, 1, ?_⟩⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [hcomm h]
  · intro m hm v hv g _
    rw [hcpow] at hv
    have h2 : (2 : ℚ) ^ m ≠ 1 := by
      have : (1 : ℚ) < 2 ^ m := one_lt_pow₀ (by norm_num) (Nat.pos_iff_ne_zero.mp hm)
      exact ne_of_gt this
    have hv0 : v = 0 := by
      have : ((2 : ℚ) ^ m - 1) * v = 0 := by rw [sub_mul, hv, one_mul, sub_self]
      rcases mul_eq_zero.mp this with h | h
      · exact absurd (sub_eq_zero.mp h) h2
      · exact h
    rw [hv0, map_zero]
  · change -(1 : ℚ) ≠ 1
    norm_num

end WildTameDescent
