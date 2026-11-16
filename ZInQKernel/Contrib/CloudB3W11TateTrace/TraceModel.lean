/-
Released under Apache 2.0 license as described in LICENSE.
Adapted from anthropics/fermats-last-theorem, commit 6e837e75,
Definitions/Def_PadicComplex_TateTrace.lean. The upstream file carries no
in-file author header; upstream NOTICE and ATTRIBUTION.md are retained by
the W11 integration. Only the import has changed.
-/
import ZInQKernel.Contrib.CloudB3W11AxCompletion.GaloisAction

set_option autoImplicit false

noncomputable section

namespace PadicComplex

variable (p : ℕ) [Fact p.Prime]

/-- Closure in the genuine `C_p` of the union of the given algebraic tower. -/
def towerClosure (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) : Set ℂ_[p] :=
  closure (⋃ m : ℕ, Set.range fun k : Km m => ((k : PadicAlgCl p) : ℂ_[p]))

/-- The actual normalized Tate trace properties, including its uniform
ramification estimate.  This structure is data required of a trace, not an
axiom or a claim that such a trace exists. -/
structure IsTateTrace (Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)) (m : ℕ) (d : ℝ)
    (R : ℂ_[p] → ℂ_[p]) : Prop where
  map_add : ∀ x ∈ towerClosure p Km, ∀ y ∈ towerClosure p Km, R (x + y) = R x + R y
  map_mul_left : ∀ (k : Km m), ∀ x ∈ towerClosure p Km,
    R (((k : PadicAlgCl p) : ℂ_[p]) * x) = ((k : PadicAlgCl p) : ℂ_[p]) * R x
  apply_coe : ∀ k : Km m, R ((k : PadicAlgCl p) : ℂ_[p]) = ((k : PadicAlgCl p) : ℂ_[p])
  exists_eq_coe : ∀ x ∈ towerClosure p Km, ∃ k : Km m, R x = ((k : PadicAlgCl p) : ℂ_[p])
  apply_smul : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (Km m).fixingSubgroup →
    ∀ x ∈ towerClosure p Km, R (σ • x) = R x
  norm_sub_apply_le : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ (Km m).fixingSubgroup →
    σ ∉ (Km (m + 1)).fixingSubgroup → ∀ x ∈ towerClosure p Km, ‖x - R x‖ ≤ d * ‖σ • x - x‖

end PadicComplex

end
