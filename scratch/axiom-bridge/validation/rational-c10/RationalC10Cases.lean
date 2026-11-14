import RationalC10Link
import RationalC10ExpectedTypes

/-
UNCOMPILED PRIVATE POSITIVE CASES.
Self-comparison uses the actual SAME native endomorphism and constructed finite
Tate bases, not caller Free/Finite or an assumed trace equality. The two primary
applications are fully general conditional types, not arithmetic instances of
C9/reduction/descent/continuity/semisimplicity. No numerical zero trace, rank,
nonzero variety or empty basis is claimed from these symbolic cases.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped MonObj TensorProduct
open PkgI3 GlueC10Link
open AxiomBridge.NativeEndTrace

namespace RationalC10Cases

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Use actual endE, N=1 and Phi=id; construct finite target data from the
already checked original Tate supplier under the original allowed-prime guard. -/
theorem selfComparison {k : Type} [Field k] (A : AbVar k) (α : AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : k) ≠ 0)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] :
    LinearMap.trace E (E ⊗[ℚ_[ℓ]] A.V ℓ) (endE α ℓ E) =
      (rationalTrace A α : E) := by
  have hA := AxiomBridge.TateConsumer.tate_free_finite A ℓ hℓ
  letI := hA.1
  letI := hA.2
  let b := (Module.Free.chooseBasis ℤ_[ℓ] (A.T ℓ)).baseChange ℚ_[ℓ]
  letI := Module.Free.of_basis b
  letI := Module.Finite.of_basis b
  let bE := b.baseChange E
  letI := Module.Free.of_basis bE
  letI := Module.Finite.of_basis bE
  have hcmp : FrobCompare ℓ (endE α ℓ E) α 1 :=
    ⟨LinearEquiv.refl E _, by simp⟩
  simpa using
    AxiomBridge.RationalC10Link.trace_T_of_frobCompare A α ℓ hℓ (endE α ℓ E) 1 hcmp

/-- Same A/alpha under both actual further extensions, with one rational image
in a supplied C; no independent per-prime endomorphism or desired trace Fact. -/
theorem sameThreeFiveSelfComparison {k : Type} [Field k]
    (A : AbVar k) (α : AbVar.End A) (h3 : (3 : k) ≠ 0) (h5 : (5 : k) ≠ 0)
    (C : Type) [Field C] [CharZero C]
    (E₃ : Type) [Field E₃] [Algebra ℚ_[3] E₃] (j₃ : C →+* E₃)
    (E₅ : Type) [Field E₅] [Algebra ℚ_[5] E₅] (j₅ : C →+* E₅) :
    ∃ t : C,
      LinearMap.trace E₃ (E₃ ⊗[ℚ_[3]] A.V 3) (endE α 3 E₃) = j₃ t ∧
      LinearMap.trace E₅ (E₅ ⊗[ℚ_[5]] A.V 5) (endE α 5 E₅) = j₅ t := by
  letI : CharZero E₃ := charZero_of_injective_ringHom j₃.injective
  letI : CharZero E₅ := charZero_of_injective_ringHom j₅.injective
  refine ⟨(rationalTrace A α : C), ?_, ?_⟩
  · simpa only [map_ratCast] using selfComparison A α 3 h3 E₃
  · simpa only [map_ratCast] using selfComparison A α 5 h5 E₅

-- Actual dyadic and allowed-positive-characteristic native applications.
example (A : AbVar ℚ) (α : AbVar.End A) :
    LinearMap.trace ℚ_[2] (ℚ_[2] ⊗[ℚ_[2]] A.V 2) (endE α 2 ℚ_[2]) =
      (rationalTrace A α : ℚ_[2]) :=
  selfComparison A α 2 (by norm_num) ℚ_[2]

example (A : AbVar (ZMod 3)) (α : AbVar.End A) :
    LinearMap.trace ℚ_[5] (ℚ_[5] ⊗[ℚ_[5]] A.V 5) (endE α 5 ℚ_[5]) =
      (rationalTrace A α : ℚ_[5]) :=
  selfComparison A α 5 (by decide) ℚ_[5]

example (A : AbVar ℚ) (α : AbVar.End A) :
    ∃ t : ℚ,
      LinearMap.trace ℚ_[3] (ℚ_[3] ⊗[ℚ_[3]] A.V 3) (endE α 3 ℚ_[3]) =
        algebraMap ℚ ℚ_[3] t ∧
      LinearMap.trace ℚ_[5] (ℚ_[5] ⊗[ℚ_[5]] A.V 5) (endE α 5 ℚ_[5]) =
        algebraMap ℚ ℚ_[5] t :=
  sameThreeFiveSelfComparison A α (by norm_num) (by norm_num) ℚ
    ℚ_[3] (algebraMap ℚ ℚ_[3]) ℚ_[5] (algebraMap ℚ ℚ_[5])

-- Exact complete conditional consumer application, not constructed arithmetic data.
example : RationalC10Checks.expectedC10TraceLink :=
  AxiomBridge.RationalC10Link.c10_of_trace_link

example : RationalC10Checks.expectedC10Squares :=
  AxiomBridge.RationalC10Link.c10_of_squares

end RationalC10Cases

#print axioms RationalC10Cases.selfComparison
#print axioms RationalC10Cases.sameThreeFiveSelfComparison
