# Implementation note: One active state per time slot

- Lean name: `ZInQ.Compiler.Packed.one_active_state`.
- Draft:
  ```lean
  theorem one_active_state (B q m : ℕ) (hm : m < B) (σ : Fin m → ℕ → ℕ)
      (hσ : ∀ i t, σ i t ≤ 1) (hsum : ∑ i, ∑ t in range (q+1), σ i t * B^t = ∑ t in range (q+1), B^t)
      (hlast : ∑ t in range (q+1), σ ⟨m-1, _⟩ t * B^t = B^q) :
      ∀ t ≤ q, (∃! i, σ i t = 1) ∧ (σ ⟨m-1,_⟩ t = 1 ↔ t = q)
  ```
- Mathlib: `Finset.sum_comm`, `Nat.ofDigits_inj_of_len_eq` (or the local base-`B` uniqueness).
- Upstream reuse: none directly. `PackedRegister.digits_eq_of_sum_eq` is `private` and
  `lean/` is kept unchanged, so reprove the base-`B` uniqueness lemma once in
  `ZInQKernel` and share it with the masked-digit and transition articles.
- FINITE COMPUTATION: no. Difficulty: easy-medium.
