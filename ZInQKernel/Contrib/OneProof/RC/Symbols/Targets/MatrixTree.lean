import ZInQKernel.Contrib.OneProof.RC.Symbols.Core
namespace ZInQ.Manuscript.RC.Symbols
open Finset Matrix
variable {L : Type*} [AddCommGroup L]

open Classical in
/-- All-minors matrix-tree theorem mod 2, degree zero (tex 10641–10650; Chaiken 1982). -/
theorem mt0 (Γ : Config L) (T X : Finset ℕ) (hTX : Disjoint T X)
    (hsymm : ∀ x ∈ X, ∀ u ∈ T ∪ X, x ≠ u → Γ.z x u = Γ.z u x) :
    (((netEdges Γ T X).powerset.filter
        (fun S => IsRootedForest T X S ∧ starForest T S = ∅)).card : ZMod 2) =
      (lap Γ T X).det := sorry

open Classical in
/-- All-minors matrix-tree theorem mod 2, degree one (tex 10641–10650; Chaiken 1982). -/
theorem mt1 (Γ : Config L) (T X : Finset ℕ) (hTX : Disjoint T X)
    (hsymm : ∀ x ∈ X, ∀ u ∈ T ∪ X, x ≠ u → Γ.z x u = Γ.z u x)
    {a c : ℕ} (ha : a ∈ T) (hc : c ∈ T) (hac : a ≠ c) :
    (((netEdges Γ T X).powerset.filter
        (fun S => IsRootedForest T X S ∧ starForest T S = {s(a, c)})).card : ZMod 2) =
      attach Γ X a ⬝ᵥ ((lap Γ T X).adjugate *ᵥ attach Γ X c) := sorry
end ZInQ.Manuscript.RC.Symbols
