import Mathlib

/-!
# bdr-kertheta: `ker θ` is principal

Part A: a complete-Nakayama criterion for the kernel of a ring map out of a `p`-adically complete
ring. Part B: inverting `p`. Part C: Fontaine's `θ` for a general `p`-adically complete `O`,
reduced to one divisibility statement in the tilt.
-/

open Ideal

namespace BdrKer

section PartA

variable {A B : Type*} [CommRing A] [CommRing B] (p : ℕ)

theorem mem_span_pow_iff' (n : ℕ) (x : A) :
    x ∈ (span {(p : A)} ^ n • ⊤ : Submodule A A) ↔ ∃ c, x = (p : A) ^ n * c := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, mul_comm _ _⟩
  · rintro ⟨c, rfl⟩; exact ⟨c, mul_comm _ _⟩

/-- **Part A.** If `A` is `p`-adically complete, `p` is a non-zero-divisor on `B`, and
`ker θ ⊆ ξ A + p A` for some `ξ ∈ ker θ`, then `ker θ = ξ A`. -/
theorem ker_eq_span_of_mod_p [IsAdicComplete (span {(p : A)}) A] (θ : A →+* B)
    (hB : ∀ b : B, (p : B) * b = 0 → b = 0) (ξ : A) (hξ : θ ξ = 0)
    (h : ∀ x, θ x = 0 → ∃ y z, x = ξ * y + p * z) :
    RingHom.ker θ = span {ξ} := by
  apply le_antisymm
  · intro x hx
    have h' : ∀ x : RingHom.ker θ, ∃ y : A, ∃ z : RingHom.ker θ, x.1 = ξ * y + p * z.1 := by
      intro x
      obtain ⟨y, z, hyz⟩ := h x.1 x.2
      refine ⟨y, ⟨z, ?_⟩, hyz⟩
      have : θ x.1 = 0 := x.2
      rw [hyz, map_add, map_mul, map_mul, hξ, zero_mul, zero_add, map_natCast] at this
      exact hB _ this
    choose Y Z hYZ using h'
    let s : ℕ → RingHom.ker θ := fun n => Nat.rec ⟨x, hx⟩ (fun _ w => Z w) n
    let S : ℕ → A := fun n => ∑ k ∈ Finset.range n, (p : A) ^ k * Y (s k)
    have hS : ∀ n, x = ξ * S n + (p : A) ^ n * (s n).1 := by
      intro n
      induction n with
      | zero => simp [S, s]
      | succ n ih =>
        have e : (s (n + 1)) = Z (s n) := rfl
        rw [ih, hYZ (s n), ← e]
        simp only [S, Finset.sum_range_succ]
        ring
    have hdiff : ∀ m d, ∃ c, S (m + d) - S m = (p : A) ^ m * c := by
      intro m d
      induction d with
      | zero => exact ⟨0, by simp⟩
      | succ d ih =>
        obtain ⟨c, hc⟩ := ih
        refine ⟨c + (p : A) ^ d * Y (s (m + d)), ?_⟩
        have : S (m + (d + 1)) = S (m + d) + (p : A) ^ (m + d) * Y (s (m + d)) := by
          simp only [S, ← add_assoc, Finset.sum_range_succ]
        rw [this, pow_add]
        linear_combination hc
    have hcauchy : ∀ {m n}, m ≤ n →
        S m ≡ S n [SMOD (span {(p : A)} ^ m • ⊤ : Submodule A A)] := by
      intro m n hmn
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [SModEq.sub_mem, mem_span_pow_iff']
      obtain ⟨c, hc⟩ := hdiff m d
      exact ⟨-c, by linear_combination -hc⟩
    obtain ⟨L, hL⟩ := IsPrecomplete.prec inferInstance hcauchy
    have hx : x = ξ * L := by
      rw [← sub_eq_zero]
      apply IsHausdorff.haus' (I := span {(p : A)})
      intro n
      rw [SModEq.sub_mem, sub_zero, mem_span_pow_iff']
      have := hL n
      rw [SModEq.sub_mem, mem_span_pow_iff'] at this
      obtain ⟨c, hc⟩ := this
      refine ⟨ξ * c + (s n).1, ?_⟩
      linear_combination hS n + ξ * hc
    rw [hx]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ξ)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hξ

end PartA

end BdrKer
