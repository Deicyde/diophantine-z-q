/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_Submodule_finite_torsionBy_pow_of_finite_torsionBy (git blob c88cc7a810132049c5beeff03d7cd27e482e5399, sha256 6235f8b07a84be59a4b9e44f69c04369309dfd0a6541d0d58a9f70bf2ff9bace).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_Submodule_finite_torsionBy_pow_of_finite_torsionBy

set_option maxHeartbeats 1600000
set_option autoImplicit false

theorem solution
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (a : R)
    (h : Finite (Submodule.torsionBy R M a)) (k : ℕ) :
    Finite (Submodule.torsionBy R M (a ^ k)) := by
  have hS : {x : M | a • x = 0}.Finite := by
    have : {x : M | a • x = 0} = (Submodule.torsionBy R M a : Set M) := by
      ext x; simp
    rw [this]
    exact Set.toFinite _
  suffices H : ∀ k : ℕ, {x : M | a ^ k • x = 0}.Finite by
    have hk := H k
    have : {x : M | a ^ k • x = 0} = (Submodule.torsionBy R M (a ^ k) : Set M) := by
      ext x; simp
    rw [this] at hk
    exact hk.to_subtype
  intro k
  induction k with
  | zero =>
      refine (Set.finite_singleton (0 : M)).subset ?_
      intro x hx
      simpa using hx
  | succ k ih =>

      have hfib : ∀ y : M, {x : M | a ^ k • x = y}.Finite := by
        intro y
        rcases Set.eq_empty_or_nonempty {x : M | a ^ k • x = y} with he | ⟨x₀, hx₀⟩
        · rw [he]; exact Set.finite_empty
        · refine (ih.image fun s => x₀ + s).subset ?_
          intro x hx
          simp only [Set.mem_setOf_eq] at hx hx₀
          refine ⟨x - x₀, ?_, by abel⟩
          simp only [Set.mem_setOf_eq, smul_sub, hx, hx₀, sub_self]

      refine (hS.biUnion fun y _ => hfib y).subset ?_
      intro x hx
      simp only [Set.mem_setOf_eq] at hx
      refine Set.mem_biUnion (x := a ^ k • x) ?_ rfl
      simp only [Set.mem_setOf_eq, smul_smul, ← pow_succ', hx]
