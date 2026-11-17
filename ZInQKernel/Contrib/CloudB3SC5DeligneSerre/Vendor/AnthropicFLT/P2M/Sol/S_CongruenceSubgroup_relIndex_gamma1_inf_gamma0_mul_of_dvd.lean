/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CongruenceSubgroup_relIndex_gamma1_inf_gamma0_mul_of_dvd (git blob 84ed483bbceaa40d1e0660b13686959ae68f3753, sha256 f5a18fd64890b0f494fd07ec2aa00b25ff141fa6c6048773132ae7b7b4e2be7e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CongruenceSubgroup_relIndex_gamma1_inf_gamma0_mul_of_dvd

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

namespace IndexDvd

variable {M : ℕ}

private theorem dvd_entry (γ : ↥(Gamma1 M)) : (M : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 := by
  have h := ((Gamma1_mem M γ).mp γ.2).2.2
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h

variable (M) (q : ℕ)

private noncomputable def cHom [NeZero M] (hq : q ∣ M) : ↥(Gamma1 M) →* Multiplicative (ZMod q) where
  toFun γ := Multiplicative.ofAdd ((((γ : SL(2, ℤ)) 1 0 / (M : ℤ) : ℤ) : ZMod q))
  map_one' := by simp
  map_mul' γ δ := by
    obtain ⟨k₁, hk₁⟩ := dvd_entry γ
    obtain ⟨k₂, hk₂⟩ := dvd_entry δ
    have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
    have hmul : ((γ * δ : ↥(Gamma1 M)) : SL(2, ℤ)) 1 0 =
        (M : ℤ) * (k₁ * (δ : SL(2, ℤ)) 0 0 + (γ : SL(2, ℤ)) 1 1 * k₂) := by
      have h1 : ((γ * δ : ↥(Gamma1 M)) : SL(2, ℤ)) 1 0 =
          (γ : SL(2, ℤ)) 1 0 * (δ : SL(2, ℤ)) 0 0 + (γ : SL(2, ℤ)) 1 1 * (δ : SL(2, ℤ)) 1 0 := by
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [h1, hk₁, hk₂]; ring
    rw [← ofAdd_add]
    congr 1
    rw [hmul, hk₁, hk₂, Int.mul_ediv_cancel_left _ hM, Int.mul_ediv_cancel_left _ hM,
      Int.mul_ediv_cancel_left _ hM]
    have ha : (((δ : SL(2, ℤ)) 0 0 : ℤ) : ZMod q) = 1 := by
      have h := ((Gamma1_mem M δ).mp δ.2).1
      have h' := congrArg (ZMod.castHom hq (ZMod q)) h
      rwa [map_intCast, map_one] at h'
    have hd : (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod q) = 1 := by
      have h := ((Gamma1_mem M γ).mp γ.2).2.1
      have h' := congrArg (ZMod.castHom hq (ZMod q)) h
      rwa [map_intCast, map_one] at h'
    push_cast
    rw [ha, hd, mul_one, one_mul]

private theorem cHom_apply [NeZero M] (hq : q ∣ M) (γ : ↥(Gamma1 M)) :
    cHom M q hq γ = Multiplicative.ofAdd ((((γ : SL(2, ℤ)) 1 0 / (M : ℤ) : ℤ) : ZMod q)) := rfl

private theorem cHom_eq_one_iff [NeZero M] (hq : q ∣ M) (γ : ↥(Gamma1 M)) :
    cHom M q hq γ = 1 ↔ (γ : SL(2, ℤ)) ∈ Gamma0 (M * q) := by
  obtain ⟨k, hk⟩ := dvd_entry γ
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  rw [cHom_apply, ofAdd_eq_one, hk, Int.mul_ediv_cancel_left _ hM, ZMod.intCast_zmod_eq_zero_iff_dvd,
    Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd, hk, Nat.cast_mul]
  exact (mul_dvd_mul_iff_left hM).symm

private theorem cHom_surjective [NeZero M] (hq : q ∣ M) : Function.Surjective (cHom M q hq) := by
  intro x
  obtain ⟨j, hj⟩ := ZMod.intCast_surjective (Multiplicative.toAdd x)
  have hM : (M : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne M
  let A : SL(2, ℤ) := ⟨!![1, 0; (M : ℤ) * j, 1], by simp [Matrix.det_fin_two_of]⟩
  have hA : A ∈ Gamma1 M := by
    rw [Gamma1_mem]
    simp [A]
  refine ⟨⟨A, hA⟩, ?_⟩
  rw [cHom_apply]
  have h10 : ((⟨A, hA⟩ : ↥(Gamma1 M)) : SL(2, ℤ)) 1 0 = (M : ℤ) * j := by
    simp [A]
  rw [h10, Int.mul_ediv_cancel_left _ hM, hj]
  rfl

end IndexDvd

open IndexDvd in

theorem solution (M q : ℕ) [NeZero M] (hq : q ∣ M) :
    (CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * q)).relIndex (CongruenceSubgroup.Gamma1 M) = q := by
  have hker : (Gamma1 M ⊓ Gamma0 (M * q)).subgroupOf (Gamma1 M) = (cHom M q hq).ker := by
    ext γ
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, Subgroup.mem_inf, cHom_eq_one_iff]
    exact ⟨fun h => h.2, fun h => ⟨γ.2, h⟩⟩
  rw [Subgroup.relIndex, hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (cHom_surjective M q hq),
    Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
