import ZInQKernel.Contrib.OneProof.RC.Symbols.Core
namespace ZInQ.Manuscript.RC.Symbols
open Finset
variable {L : Type*} [AddCommGroup L] {ε : L →+ ZMod 2} {A : Config L → ZMod 2}

theorem act_mul (p q : MvPolynomial (Sym2 ℕ) (ZMod 2)) (f : Finset (Sym2 ℕ) → ZMod 2) :
    act (p * q) f = act p (act q f) := sorry
theorem act_add (p q : MvPolynomial (Sym2 ℕ) (ZMod 2)) (f : Finset (Sym2 ℕ) → ZMod 2) :
    act (p + q) f = fun U => act p f U + act q f U := sorry
theorem act_one (f : Finset (Sym2 ℕ) → ZMod 2) : act 1 f = f := sorry

/-- Network expansion (tex 10635–10650): expand in the auxiliary bits, contract forests;
terminal-free components vanish by primary isolation. -/
theorem netOp_expansion (hA : CoefficientRules ε A) (Γ : Config L) (hΓ : Γ.Compatible ε)
    (T X : Finset ℕ) (hV : Γ.V = T ∪ X) (hTX : Disjoint T X) (hX : ∀ x ∈ X, Γ.t x = 0) :
    A Γ = act (netOp Γ T X) (fun U => A ((Γ.restrict T).flipBy U)) ∅ := sorry

/-- Distinct networks multiply (tex 10651–10655). -/
theorem netOp_expansion_multi (hA : CoefficientRules ε A) (Γ : Config L) (hΓ : Γ.Compatible ε)
    (T : Finset ℕ) {κ : Type*} (N : Finset κ) (Xf : κ → Finset ℕ)
    (hV : Γ.V = T ∪ N.biUnion Xf) (hTX : ∀ ν ∈ N, Disjoint T (Xf ν))
    (hdisj : ∀ ν ∈ N, ∀ μ ∈ N, ν ≠ μ → Disjoint (Xf ν) (Xf μ))
    (hX : ∀ ν ∈ N, ∀ x ∈ Xf ν, Γ.t x = 0)
    (hsep : ∀ ν ∈ N, ∀ μ ∈ N, ν ≠ μ → ∀ x ∈ Xf ν, ∀ y ∈ Xf μ, Γ.z x y = 0) :
    A Γ = act (∏ ν ∈ N, netOp Γ T (Xf ν)) (fun U => A ((Γ.restrict T).flipBy U)) ∅ := sorry

open Classical in
theorem netOp_constantCoeff (Γ : Config L) (T X : Finset ℕ) :
    MvPolynomial.constantCoeff (netOp Γ T X) =
      (((netEdges Γ T X).powerset.filter
        (fun S => IsRootedForest T X S ∧ starForest T S = ∅)).card : ZMod 2) := sorry

open Classical in
theorem netOp_coeff_X (Γ : Config L) (T X : Finset ℕ) {a c : ℕ} (ha : a ∈ T) (hc : c ∈ T)
    (hac : a ≠ c) :
    (netOp Γ T X).coeff (Finsupp.single s(a, c) 1) =
      (((netEdges Γ T X).powerset.filter
        (fun S => IsRootedForest T X S ∧ starForest T S = {s(a, c)})).card : ZMod 2) := sorry
end ZInQ.Manuscript.RC.Symbols
