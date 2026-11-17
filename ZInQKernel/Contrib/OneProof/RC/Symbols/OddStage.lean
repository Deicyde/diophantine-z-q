import ZInQKernel.Contrib.OneProof.RC.Symbols.Stabilization

/-!
# Lane RC2: consequences of the odd-table stabilization (tex 10508–10552)
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset

variable {L : Type*} [AddCommGroup L]

/-- **`ex:app-odd-stabilization`, witness and common stage clauses** (tex 10517–10523,
10545–10548). Kind: PROVED from `odd_stabilization`. The intrinsic odd symbol satisfies the
coefficient rules on all compatible finite typed graphs; a graph that is a unit at the stages of a
set in the ultrafilter (the bounded-weight witness) remains a unit of the limit symbol; and every
specified finite collection of tests has one common actual stage at which the stage table agrees
with the limit symbol. No stage common to all cutoffs is asserted. -/
theorem odd_stabilization_witness [Fintype L] [DecidableEq L] {I : Type*} (𝒰 : Ultrafilter I)
    (ε : L →+ ZMod 2) (A : I → Config L → ZMod 2)
    (hvalid : ∀ W : ℕ, ∀ᶠ i in (𝒰 : Filter I), RulesUpTo ε (A i) W) :
    ∃ Ainf : Config L → ZMod 2, CoefficientRules ε Ainf ∧
      (∀ Γ₀ : Config L, Γ₀.Compatible ε → (∀ᶠ i in (𝒰 : Filter I), A i Γ₀ = 1) → Ainf Γ₀ = 1) ∧
      ∀ (n : ℕ) (Γs : Fin n → Config L), (∀ k, (Γs k).Compatible ε) →
        ∃ i, ∀ k, A i (Γs k) = Ainf (Γs k) := by
  obtain ⟨Ainf, hrules, hagree⟩ := odd_stabilization 𝒰 ε A hvalid
  refine ⟨Ainf, hrules, ?_, ?_⟩
  · intro Γ₀ hΓ₀ hunit
    have h1 := hagree 1 (fun _ => Γ₀) (fun _ => hΓ₀)
    obtain ⟨i, hi1, hi2⟩ := (h1.and hunit).exists
    rw [← hi1 0, hi2]
  · intro n Γs hΓs
    exact (hagree n Γs hΓs).exists

end ZInQ.Manuscript.RC.Symbols
