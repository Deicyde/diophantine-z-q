/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AutomorphicForm_SigmaCentralizer (git blob f4b4114e0de109266685fc3b0214e4545678b212, sha256 a958858ec885075e0226811ac47f5735db1f644501094cf99b5da1996562dcd5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

namespace AutomorphicForm

variable {G : Type*} [Group G]

def sigmaCentralizer (σ : G →* G) (δ : G) : Subgroup G where
  carrier := {t | t * δ * (σ t)⁻¹ = δ}
  one_mem' := by
    simp only [Set.mem_setOf_eq, one_mul, map_one, inv_one, mul_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have key : a * b * δ * (σ (a * b))⁻¹ = a * (b * δ * (σ b)⁻¹) * (σ a)⁻¹ := by
      simp only [map_mul, mul_inv_rev]
      group
    rw [key, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [map_inv, inv_inv]
    have h2 : δ * σ a = a * δ := by
      calc δ * σ a = (a * δ * (σ a)⁻¹) * σ a := by rw [ha]
        _ = a * δ := by group
    calc a⁻¹ * δ * σ a = a⁻¹ * (δ * σ a) := by group
      _ = a⁻¹ * (a * δ) := by rw [h2]
      _ = δ := by group

@[simp] theorem mem_sigmaCentralizer_iff {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ t * δ * (σ t)⁻¹ = δ := Iff.rfl

theorem mem_sigmaCentralizer_iff_fixed {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ δ * σ t * δ⁻¹ = t := by
  rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem mem_sigmaCentralizer_iff_inv {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ t⁻¹ * δ * σ t = δ := by
  rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact eq_comm

theorem sigmaCentralizer_id (δ : G) :
    sigmaCentralizer (MonoidHom.id G) δ = Subgroup.centralizer {δ} := by
  ext t
  rw [mem_sigmaCentralizer_iff, Subgroup.mem_centralizer_singleton_iff, MonoidHom.id_apply,
    mul_inv_eq_iff_eq_mul]

theorem sigmaCentralizer_one_eq_bot (δ : G) :
    sigmaCentralizer (1 : G →* G) δ = ⊥ := by
  ext t
  rw [mem_sigmaCentralizer_iff, Subgroup.mem_bot]
  constructor
  · intro h
    have h1 : t * δ = δ := by
      simpa using h
    exact mul_right_cancel (by rw [one_mul]; exact h1)
  · rintro rfl
    simp
