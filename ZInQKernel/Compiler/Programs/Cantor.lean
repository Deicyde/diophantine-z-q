import ZInQ.CantorDecoder
import Mathlib

/-!
# Cantor pairing and unique unpairing

Blueprint: `compiler/natural/programs/cantor-pairing.md` and `cantor-unpairing.md`.

The pairing `pair(a, b) = (a + b)(a + b + 1)/2 + b`, its decoder loop, `unpair = decode`,
`enc₅` and `dec₅` are upstream's `ZInQ.CantorDecoder.pair`, `loop`, `decode`, `encode5`,
`decode5`; items 1–3 of the unpairing statement are upstream's theorems, collected below,
and item 4 (the pairing system) is `pairing_system_iff`.
-/

namespace ZInQ.Compiler.IR

open CantorDecoder

/-- Item 1: `2 pair(a, b) = (a + b)(a + b + 1) + 2b`, the triangular interval, and
bijectivity. -/
theorem cantor_pair_props :
    (∀ a b, 2 * pair a b = (a + b) * (a + b + 1) + 2 * b) ∧
    (∀ a b, (a + b) * (a + b + 1) / 2 ≤ pair a b) ∧
    (∀ a b, pair a b < (a + b + 1) * (a + b + 2) / 2) ∧
    Function.Bijective (fun p : ℕ × ℕ => pair p.1 p.2) := by
  refine ⟨two_mul_pair, tri_le_pair, ?_, ?_, ?_⟩
  · intro a b
    have := pair_lt_tri_succ a b
    simpa [Nat.add_assoc] using this
  · rintro ⟨a, b⟩ ⟨c, d⟩ h
    obtain ⟨h1, h2⟩ := pair_inj h
    simp only at h1 h2; rw [h1, h2]
  · intro x
    exact ⟨decode x, pair_decode x⟩

/-- Item 2: `unpair ∘ pair = id`, `pair ∘ unpair = id`, and the same for `enc₅`, `dec₅`. -/
theorem cantor_unpair_props :
    (∀ a b, decode (pair a b) = (a, b)) ∧ (∀ x, pair (decode x).1 (decode x).2 = x) ∧
    (∀ a b c d e, decode5 (encode5 a b c d e) = (a, b, c, d, e)) ∧
    (∀ x, encode5 (decode5 x).1 (decode5 x).2.1 (decode5 x).2.2.1 (decode5 x).2.2.2.1
      (decode5 x).2.2.2.2 = x) :=
  ⟨decode_pair, pair_decode, decode5_encode5, encode5_decode5⟩

/-- Item 3: `2t - (a + b)(a + b + 1) - 2b = 0` in `ℤ` iff `t = pair(a, b)`. -/
theorem cantor_pairing_equation (a b t : ℕ) :
    (2 * (t : ℤ) - ((a : ℤ) + b) * ((a : ℤ) + b + 1) - 2 * (b : ℤ) = 0) ↔ t = pair a b :=
  pairing_equation_iff a b t

/-- The successor value in the pairing system: `t_{i+1}`, with `t₄ = c₄`. -/
def tNext (t : Fin 4 → ℕ) (c : Fin 5 → ℕ) (i : Fin 4) : ℕ :=
  if h : i.val = 3 then c 4 else t ⟨i.val + 1, by omega⟩

/-- Item 4: with `t₄ = c₄`, the four pairing equations `2tᵢ = (cᵢ + tᵢ₊₁)(cᵢ + tᵢ₊₁ + 1) +
2tᵢ₊₁` hold exactly for `tᵢ = pair(cᵢ, tᵢ₊₁)`, and then `t₀ = enc₅(c)`. -/
theorem pairing_system_iff (c : Fin 5 → ℕ) (t : Fin 4 → ℕ) :
    (∀ i : Fin 4, 2 * (t i : ℤ) - ((c i.castSucc : ℤ) + tNext t c i) *
        ((c i.castSucc : ℤ) + tNext t c i + 1) - 2 * (tNext t c i : ℤ) = 0) ↔
      t 3 = pair (c 3) (c 4) ∧ t 2 = pair (c 2) (t 3) ∧ t 1 = pair (c 1) (t 2) ∧
        t 0 = pair (c 0) (t 1) := by
  constructor
  · intro h
    have h3 := (pairing_equation_iff _ _ _).mp (h 3)
    have h2 := (pairing_equation_iff _ _ _).mp (h 2)
    have h1 := (pairing_equation_iff _ _ _).mp (h 1)
    have h0 := (pairing_equation_iff _ _ _).mp (h 0)
    exact ⟨h3, h2, h1, h0⟩
  · rintro ⟨h3, h2, h1, h0⟩ i
    apply (pairing_equation_iff _ _ _).mpr
    fin_cases i <;> simp [tNext, h0, h1, h2, h3]

/-- The unique solution of the pairing system has `t₀ = enc₅(c)`. -/
theorem pairing_system_encode (c : Fin 5 → ℕ) (t : Fin 4 → ℕ)
    (h : t 3 = pair (c 3) (c 4) ∧ t 2 = pair (c 2) (t 3) ∧ t 1 = pair (c 1) (t 2) ∧
        t 0 = pair (c 0) (t 1)) :
    t 0 = encode5 (c 0) (c 1) (c 2) (c 3) (c 4) := by
  obtain ⟨h3, h2, h1, h0⟩ := h
  rw [h0, h1, h2, h3]; rfl

end ZInQ.Compiler.IR
