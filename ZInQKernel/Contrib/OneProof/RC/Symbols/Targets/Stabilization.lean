import ZInQKernel.Contrib.OneProof.RC.Symbols.Core
namespace ZInQ.Manuscript.RC.Symbols
open Finset
variable {L : Type*} [AddCommGroup L]

/-- The coefficient rules on configurations with at most `W+1` vertices: the rules valid at one
finite odd stage for the cutoff `W` (tex 10533–10538). -/
structure RulesUpTo (ε : L →+ ZMod 2) (A : Config L → ZMod 2) (W : ℕ) : Prop where
  graph_dependence : ∀ Γ Δ : Config L, Γ.V.card ≤ W + 1 → Γ.Compatible ε → Γ.IsIso Δ → A Γ = A Δ
  contraction : ∀ Γ : Config L, Γ.V.card ≤ W + 1 → Γ.Compatible ε → ∀ v ∈ Γ.V, ∀ w ∈ Γ.V,
    v ≠ w → A Γ + A (Γ.flip v w) = A (Γ.contract v w)
  primary_isolation : ∀ Γ : Config L, Γ.V.card ≤ W + 1 → Γ.Compatible ε → ∀ v ∈ Γ.V,
    Γ.t v = 0 → (∀ w ∈ Γ.V, w ≠ v → Γ.z v w = 0 ∧ Γ.z w v = 0) → A Γ = 0

/-- Bounded abstract label data stabilize on the ultrafilter (tex 10510–10512, 10527–10532). -/
theorem label_type_stabilizes {I α : Type*} [Finite α] (𝒰 : Ultrafilter I) (f : I → α) :
    ∃ a, ∀ᶠ i in (𝒰 : Filter I), f i = a := sorry

/-- `ex:app-odd-stabilization` (tex 10508–10552). -/
theorem odd_stabilization [Fintype L] [DecidableEq L] {I : Type*} (𝒰 : Ultrafilter I)
    (ε : L →+ ZMod 2) (A : I → Config L → ZMod 2)
    (hvalid : ∀ W : ℕ, ∀ᶠ i in (𝒰 : Filter I), RulesUpTo ε (A i) W) :
    ∃ Ainf : Config L → ZMod 2, CoefficientRules ε Ainf ∧
      ∀ (n : ℕ) (Γs : Fin n → Config L), (∀ k, (Γs k).Compatible ε) →
        ∀ᶠ i in (𝒰 : Filter I), ∀ k, A i (Γs k) = Ainf (Γs k) := sorry
end ZInQ.Manuscript.RC.Symbols
