/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem (git blob b82e7318a94efa8a57aaddc7e8bbe99a985186be, sha256 b5a68e1d09abe9b9d58a71990e850034557ebe1d8ac0a09a2492d5a1bdc174ff).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm_det

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_NumberField_TateGlobal_ideleNorm_det_eq_one_of_isCompact_of_mem

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.TateGlobal

theorem solution
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (u : AdelicGL2 (𝓞 F) F) (hu : u ∈ U) :
    ideleNorm F (Matrix.GeneralLinearGroup.det u) = 1 := by

  have hcont : Continuous fun g : AdelicGL2 (𝓞 F) F => ideleNorm F (Matrix.GeneralLinearGroup.det g) :=
    NumberField.TateGlobal.continuous_ideleNorm_det F
  have hmul : ∀ a b : AdelicGL2 (𝓞 F) F, ideleNorm F (Matrix.GeneralLinearGroup.det (a * b)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det a) * ideleNorm F (Matrix.GeneralLinearGroup.det b) := by
    intro a b; rw [map_mul, ideleNorm_mul]
  have hpow : ∀ (n : ℕ), ideleNorm F (Matrix.GeneralLinearGroup.det (u ^ n)) =
      ideleNorm F (Matrix.GeneralLinearGroup.det u) ^ n := by
    intro n
    induction n with
    | zero => simp [NumberField.TateGlobal.ideleNorm]
    | succ n ih => rw [pow_succ u n, hmul, ih, ← pow_succ]

  obtain ⟨M, hM⟩ := (hU.image hcont).isBounded.bddAbove
  have hbd : ∀ g ∈ U, ideleNorm F (Matrix.GeneralLinearGroup.det g) ≤ M := fun g hg => hM ⟨g, hg, rfl⟩
  set x := ideleNorm F (Matrix.GeneralLinearGroup.det u) with hx
  have hxpos : 0 < x := ideleNorm_pos _

  have hup : ∀ n : ℕ, x ^ n ≤ M := fun n => by rw [← hpow]; exact hbd _ (U.pow_mem hu n)
  have hinv : ideleNorm F (Matrix.GeneralLinearGroup.det u⁻¹) = x⁻¹ := by
    have h1 : ideleNorm F (Matrix.GeneralLinearGroup.det (u * u⁻¹)) = 1 := by
      rw [mul_inv_cancel]; simp [NumberField.TateGlobal.ideleNorm]
    rw [hmul] at h1
    exact (eq_inv_of_mul_eq_one_right h1)
  have hpow' : ∀ n : ℕ, ideleNorm F (Matrix.GeneralLinearGroup.det (u⁻¹ ^ n)) = x⁻¹ ^ n := by
    intro n
    induction n with
    | zero => simp [NumberField.TateGlobal.ideleNorm]
    | succ n ih => rw [pow_succ u⁻¹ n, hmul, ih, hinv, ← pow_succ]
  have hdown : ∀ n : ℕ, x⁻¹ ^ n ≤ M := fun n => by
    rw [← hpow']; exact hbd _ (U.pow_mem (U.inv_mem hu) n)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  ·
    have h1 : 1 < x⁻¹ := (one_lt_inv₀ hxpos).mpr hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M h1
    exact absurd (hdown n) (not_le.mpr hn)
  · obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M hgt
    exact absurd (hup n) (not_le.mpr hn)
