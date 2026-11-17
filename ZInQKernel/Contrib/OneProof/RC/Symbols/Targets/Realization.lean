import ZInQKernel.Contrib.OneProof.RC.Symbols.Core
namespace ZInQ.Manuscript.RC.Symbols
open Finset

open Classical in
/-- Residue bit `z = 0` or `1` as `(a/q) = 1` or `-1` (tex 2033–2034). -/
noncomputable def legBit (a : ℤ) (q : ℕ) : ZMod 2 := if IsSquare (a : ZMod q) then 0 else 1

/-- Reverse bits by reciprocity (tex 2037–2041). -/
theorem legBit_reciprocity {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) : legBit p q + legBit q p = ((p / 2 : ℕ) : ZMod 2) * ((q / 2 : ℕ) : ZMod 2) :=
  sorry

/-- The typed graph of distinct odd primes is compatible. -/
noncomputable def primeConfig {L : Type*} (V : Finset ℕ) (t : ℕ → L) : Config L :=
  ⟨V, t, fun v w => legBit v w⟩
theorem primeConfig_compatible {L : Type*} [AddCommGroup L] (ε : L →+ ZMod 2) (V : Finset ℕ)
    (hV : ∀ p ∈ V, p.Prime ∧ p ≠ 2) (t : ℕ → L) (ht : ∀ p ∈ V, ε (t p) = ((p / 2 : ℕ) : ZMod 2)) :
    (primeConfig V t).Compatible ε := sorry

/-- Finite realization (`ex:sec7-realization`, tex 2151–2174). -/
theorem finite_realization (m : ℕ) (hm : 0 < m) (h2 : 2 ∣ m) (old : Finset ℕ)
    (hold : ∀ p ∈ old, p.Prime ∧ Nat.Coprime p m) (avoid : Finset ℕ) (n : ℕ)
    (cls : Fin n → ZMod m) (hcls : ∀ i, IsUnit (cls i))
    (bitOld : Fin n → ℕ → ZMod 2) (bitNew : Fin n → Fin n → ZMod 2) :
    ∃ q : Fin n → ℕ, Function.Injective q ∧
      (∀ i, (q i).Prime ∧ q i ∉ old ∧ q i ∉ avoid ∧ ((q i : ℕ) : ZMod m) = cls i) ∧
      (∀ i, ∀ p ∈ old, legBit (q i) p = bitOld i p) ∧
      (∀ i j, j < i → legBit (q i) (q j) = bitNew i j) := sorry

/-- A product template is replaced by a fresh prime with the same type and all external
incidences (tex 2157–2159, 2170–2173). -/
theorem product_template (m : ℕ) (hm : 0 < m) (h2 : 2 ∣ m) (old : Finset ℕ)
    (hold : ∀ p ∈ old, p.Prime ∧ Nat.Coprime p m) (P : Finset ℕ)
    (hP : ∀ r ∈ P, r.Prime ∧ Nat.Coprime r m) (avoid : Finset ℕ) :
    ∃ q : ℕ, q.Prime ∧ q ∉ old ∧ q ∉ P ∧ q ∉ avoid ∧
      ((q : ℕ) : ZMod m) = ∏ r ∈ P, (r : ZMod m) ∧
      ∀ p ∈ old, p ∉ P → legBit q p = ∑ r ∈ P, legBit r p := sorry
end ZInQ.Manuscript.RC.Symbols
