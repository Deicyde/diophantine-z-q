import ZInQKernel.Contrib.OneProof.RC.Symbols.Realization

/-!
# Lane RC2: the valuation symbol of a coefficient source (`ex:sec7-symbol`, tex 2068–2100)

The coefficient rules (`CoefficientRules`) are hypotheses on an abstract function of typed
graphs. This file records the manuscript's arithmetic symbol: on an allowed positive squarefree
index `D` of the filter, `A(D) = 1` if `v₂ a(D) = δ + ω(D)` and `0` otherwise; a configuration
realized by distinct odd primes (`primeConfig`) is read at `D = ∏ p_v`. That this reading obeys
the coefficient rules is App F `ex:app-coefficient-rules` (tex 9447–9976), another lane's.
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset

variable {L : Type*} [AddCommGroup L]

open Classical in
/-- **Definition `ex:sec7-symbol`** (tex 2068–2090). Kind: definition. The `𝔽₂`-valued symbol of a
coefficient source `a` (coefficients after phase removal, as 2-adic numbers; for an odd source
the integer representative at the retained precision) and normalized depth `δ`: one exactly when
`D` is in the source's filter, `a(D) ≠ 0` and `v₂ a(D) = δ + ω(D)`; zero off the filter. -/
noncomputable def coeffSymbol (a : ℕ → ℚ_[2]) (δ : ℤ) (inFilter : ℕ → Prop) (D : ℕ) : ZMod 2 :=
  if inFilter D ∧ a D ≠ 0 ∧ Padic.valuation (a D) = δ + (D.primeFactors.card : ℤ) then 1 else 0

/-- The reading of a configuration whose vertices are distinct primes: the symbol at the Fourier
index `D = ∏_v p_v` (tex 2044–2046). -/
noncomputable def readPrimes (a : ℕ → ℚ_[2]) (δ : ℤ) (inFilter : ℕ → Prop) (Γ : Config L) :
    ZMod 2 :=
  coeffSymbol a δ inFilter (∏ v ∈ Γ.V, v)

/-- The two alternatives of `ex:sec7-symbol` are exhaustive under the coefficient lower bound
`v₂ a(D) ≥ δ + ω(D)` (tex 2086–2089: the lower bound is part of the coefficient construction):
the symbol is zero exactly when the coefficient vanishes or its valuation exceeds the depth.
Kind: PROVED. -/
theorem coeffSymbol_eq_zero_iff (a : ℕ → ℚ_[2]) (δ : ℤ) (inFilter : ℕ → Prop) {D : ℕ}
    (hF : inFilter D) (hlow : a D ≠ 0 → δ + (D.primeFactors.card : ℤ) ≤ Padic.valuation (a D)) :
    coeffSymbol a δ inFilter D = 0 ↔
      (a D = 0 ∨ δ + (D.primeFactors.card : ℤ) < Padic.valuation (a D)) := by
  classical
  unfold coeffSymbol
  constructor
  · intro h
    by_cases ha : a D = 0
    · exact Or.inl ha
    · right
      have hne : Padic.valuation (a D) ≠ δ + (D.primeFactors.card : ℤ) := by
        intro heq
        rw [if_pos ⟨hF, ha, heq⟩] at h
        exact one_ne_zero h
      exact lt_of_le_of_ne (hlow ha) (Ne.symm hne)
  · rintro (ha | hlt)
    · rw [if_neg (fun h => h.2.1 ha)]
    · rw [if_neg (fun h => absurd h.2.2 (ne_of_gt hlt))]

/-- For distinct primes the index `∏ p_v` has `ω = |V|`: the symbol's depth `δ + ω(D)` is
`δ + (number of vertices)` (tex 2071–2078, 9672). Kind: PROVED. -/
theorem card_primeFactors_prod {V : Finset ℕ} (hV : ∀ p ∈ V, p.Prime) :
    (∏ v ∈ V, v).primeFactors.card = V.card := by
  rw [Nat.primeFactors_prod hV]

end ZInQ.Manuscript.RC.Symbols
