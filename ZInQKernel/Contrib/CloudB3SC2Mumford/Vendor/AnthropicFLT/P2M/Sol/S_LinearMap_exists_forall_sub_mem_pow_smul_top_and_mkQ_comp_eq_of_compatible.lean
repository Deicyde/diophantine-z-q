/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_LinearMap_exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_LinearMap_exists_forall_sub_mem_pow_smul_top_and_mkQ_comp_eq_of_compatible

set_option autoImplicit false

universe u v w

theorem solution
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N]
    (J : ℕ → Submodule B N) (hJ : ∀ k, J (k + 1) ≤ J k)
    (hIJ : ∀ k, I ^ (k + 1) • (⊤ : Submodule B N) ≤ J k)
    (c : ℕ) (hJI : ∀ k, J (k + c) ≤ I ^ (k + 1) • (⊤ : Submodule B N))
    (f : ∀ k, M →ₗ[B] N ⧸ J k)
    (hf : ∀ k, Submodule.factor (hJ k) ∘ₗ f (k + 1) = f k) :
    ∃ g : ℕ → (M →ₗ[B] N),
      (∀ k, g (k + 1) - g k ∈ I ^ (k + 1) • (⊤ : Submodule B (M →ₗ[B] N))) ∧
      (∀ k, (J k).mkQ ∘ₗ g k = f k) := by
  classical
  obtain ⟨c₁, hZ1⟩ := LinearMap.exists_forall_exists_mkQ_comp_eq_factor_comp (B := B) I (M := M) (N := N)
  obtain ⟨c₂, hZ2⟩ := LinearMap.exists_forall_mem_pow_smul_top_of_range_le_pow_smul (B := B) I (M := M) (N := N)
  have hJle : Antitone J := antitone_nat_of_succ_le hJ
  have hIle : Antitone fun n : ℕ => I ^ n • (⊤ : Submodule B N) :=
    fun a b hab => Submodule.smul_mono_left (Ideal.pow_le_pow_right hab)

  have factor_refl : ∀ (p : Submodule B N) (y : N ⧸ p), Submodule.factor (le_refl p) y = y := by
    intro p y
    induction y using Submodule.Quotient.induction_on with
    | H x => exact Submodule.factor_mk _ x

  have hfac : ∀ (a b : ℕ) (hab : a ≤ b), Submodule.factor (hJle hab) ∘ₗ f b = f a := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact LinearMap.ext fun x => factor_refl _ _
    | succ b hab ih =>
      rw [← Submodule.factor_comp (hJ b) (hJle hab), LinearMap.comp_assoc, hf b, ih]

  have hle : ∀ n, J (n + c₁ + c) ≤ I ^ (n + c₁) • (⊤ : Submodule B N) :=
    fun n => (hJI (n + c₁)).trans (hIle (Nat.le_succ _))
  choose h hh using fun n => hZ1 n (Submodule.factor (hle n) ∘ₗ f (n + c₁ + c))

  have L : ∀ (n a : ℕ) (ha : n + c₁ + c ≤ a),
      (I ^ n • (⊤ : Submodule B N)).mkQ ∘ₗ h n =
        Submodule.factor ((hJle ha).trans ((hle n).trans (hIle (Nat.le_add_right n c₁)))) ∘ₗ f a := by
    intro n a ha
    rw [hh n, ← LinearMap.comp_assoc, Submodule.factor_comp, ← hfac _ a ha, ← LinearMap.comp_assoc, Submodule.factor_comp]
  refine ⟨fun k => h (k + 1 + c₂), fun k => ?_, fun k => ?_⟩
  ·
    apply hZ2 (k + 1)
    rw [← Submodule.ker_mkQ (I ^ (k + 1 + c₂) • (⊤ : Submodule B N)), LinearMap.range_le_ker_iff, LinearMap.comp_sub,
      sub_eq_zero]
    have e1 : (I ^ (k + 1 + c₂) • (⊤ : Submodule B N)).mkQ =
        Submodule.factor (hIle (show k + 1 + c₂ ≤ k + 1 + 1 + c₂ by omega)) ∘ₗ (I ^ (k + 1 + 1 + c₂) • (⊤ : Submodule B N)).mkQ :=
      (Submodule.factor_comp_mk _).symm
    show (I ^ (k + 1 + c₂) • (⊤ : Submodule B N)).mkQ ∘ₗ h (k + 1 + 1 + c₂) =
      (I ^ (k + 1 + c₂) • (⊤ : Submodule B N)).mkQ ∘ₗ h (k + 1 + c₂)
    rw [L (k + 1 + c₂) (k + 1 + 1 + c₂ + c₁ + c) (by omega), e1, LinearMap.comp_assoc,
      L (k + 1 + 1 + c₂) (k + 1 + 1 + c₂ + c₁ + c) le_rfl, ← LinearMap.comp_assoc, Submodule.factor_comp]
  ·
    have e2 : (J k).mkQ = Submodule.factor ((hIle (show k + 1 ≤ k + 1 + c₂ by omega)).trans (hIJ k)) ∘ₗ
        (I ^ (k + 1 + c₂) • (⊤ : Submodule B N)).mkQ := (Submodule.factor_comp_mk _).symm
    show (J k).mkQ ∘ₗ h (k + 1 + c₂) = f k
    rw [e2, LinearMap.comp_assoc, L (k + 1 + c₂) (k + 1 + c₂ + c₁ + c) le_rfl, ← LinearMap.comp_assoc, Submodule.factor_comp,
      hfac k _ (by omega)]
