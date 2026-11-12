import ZInQKernel.HDecomp.Objects

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-c10/Trace.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

/-
glue-c10: the ℓ-independence of traces (C10), over pkg-I3's definitions as imported
from `ZInQKernel.HDecomp.Objects` (§A of obj-bridge, verbatim pkg-I3).
-/
noncomputable section

namespace PkgI3

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open AbVar Polynomial
open scoped TensorProduct

/-- **C10, the characteristic-polynomial comparison (GLUE, proved from Mumford §19 Thm 4).**
For an endomorphism `φ` of an abelian variety over any field `k` there is one integer `t` that is
the trace of `V_ℓ(φ)` for every prime `ℓ ≠ char k` (N5 L788-790: "independent of the coefficient
prime"). -/
theorem trace_indep_of_ell (h : CharPolyIndepOfEll) (k : Type) [Field k] (A : AbVar k)
    (φ : End A) : ∃ t : ℤ, ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (I : Type) [Fintype I] [DecidableEq I] (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
        LinearMap.trace ℚ_[ℓ] (A.V ℓ) ((homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]) = (t : ℚ_[ℓ]) := by
  obtain ⟨P, -, hP⟩ := h k A φ
  refine ⟨-P.nextCoeff, fun ℓ _ hℓ I _ _ b => ?_⟩
  rw [LinearMap.trace_eq_matrix_trace ℚ_[ℓ] b, Matrix.trace_eq_neg_charpoly_nextCoeff,
    hP ℓ hℓ I b, Polynomial.nextCoeff_map (Int.castRingHom ℚ_[ℓ]).injective_int]
  simp

/-- The same integer for two primes: the traces at `ℓ₁` and `ℓ₂` are images of one integer. -/
theorem trace_eq_trace_of_ell (h : CharPolyIndepOfEll) (k : Type) [Field k] (A : AbVar k)
    (φ : End A) (ℓ₁ ℓ₂ : ℕ) [Fact ℓ₁.Prime] [Fact ℓ₂.Prime] (h₁ : (ℓ₁ : k) ≠ 0) (h₂ : (ℓ₂ : k) ≠ 0)
    (I₁ I₂ : Type) [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂]
    (b₁ : Module.Basis I₁ ℚ_[ℓ₁] (A.V ℓ₁)) (b₂ : Module.Basis I₂ ℚ_[ℓ₂] (A.V ℓ₂)) :
    ∃ t : ℤ, LinearMap.trace ℚ_[ℓ₁] (A.V ℓ₁) ((homT (ℓ := ℓ₁) φ).baseChange ℚ_[ℓ₁]) = t ∧
      LinearMap.trace ℚ_[ℓ₂] (A.V ℓ₂) ((homT (ℓ := ℓ₂) φ).baseChange ℚ_[ℓ₂]) = t := by
  obtain ⟨t, ht⟩ := trace_indep_of_ell h k A φ
  exact ⟨t, ht ℓ₁ h₁ I₁ b₁, ht ℓ₂ h₂ I₂ b₂⟩

end PkgI3

