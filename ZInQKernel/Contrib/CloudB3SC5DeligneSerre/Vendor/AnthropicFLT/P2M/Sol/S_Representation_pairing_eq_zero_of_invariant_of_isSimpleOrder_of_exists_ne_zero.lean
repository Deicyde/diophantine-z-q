/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero (git blob 2f8a2edd122bfbcd17f038a0f93b9c98b01afaa3, sha256 edcbbd7dee5b8977ec0c0814d2810473013d193cdf0a31ad81f75c45e7b8ced6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero

set_option autoImplicit false

theorem solution
    {k : Type*} [CommSemiring k] {K : Type*} [Group K]
    {S : Type*} [AddCommMonoid S] [Module k S] {S' : Type*} [AddCommMonoid S'] [Module k S']
    {X : Type*} [AddCommMonoid X] [Module k X]
    (ρ : Representation k K S) (ρ' : Representation k K S') [IsSimpleOrder (Subrepresentation ρ')]
    (β : S →ₗ[k] S' →ₗ[k] X) (hβ : ∀ (g : K) (s : S) (s' : S'), β (ρ g s) (ρ' g s') = β s s')
    (h0 : ∃ s' : S', s' ≠ 0 ∧ ∀ s : S, β s s' = 0) :
    β = 0 := by
  let N : Subrepresentation ρ' :=
    { toSubmodule :=
        { carrier := {s' | ∀ s : S, β s s' = 0}
          zero_mem' := fun s => by simp
          add_mem' := fun {a b} ha hb s => by simp [ha s, hb s]
          smul_mem' := fun c {a} ha s => by simp [ha s] }
      apply_mem_toSubmodule := fun g {s'} hs' s => by
        have := hβ g (ρ g⁻¹ s) s'
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
        show β s (ρ' g s') = 0
        rw [this]; exact hs' _ }
  have hmem : ∀ s' : S', s' ∈ N ↔ ∀ s : S, β s s' = 0 := fun s' => Iff.rfl
  have hN : N ≠ ⊥ := by
    obtain ⟨s', hs'0, hs'⟩ := h0
    intro h
    have hs'N : s' ∈ N := (hmem s').mpr hs'
    rw [h] at hs'N
    exact hs'0 ((Submodule.mem_bot k).mp hs'N)
  have hT : N = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top N).resolve_left hN
  ext s s'
  have : s' ∈ N := by rw [hT]; trivial
  exact (hmem s').mp this s
