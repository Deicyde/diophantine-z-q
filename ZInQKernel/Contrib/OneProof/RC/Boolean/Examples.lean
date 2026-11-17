import ZInQKernel.Contrib.OneProof.RC.Boolean.CoefficientTransfer

/-!
# Lane RC1-boolean, part 7: non-vacuity

The hypotheses of `coefficient_transfer` are jointly satisfiable, together with the bound `B` at
the nonzero addresses: `coefficientTransfer_hypotheses_satisfiable` exhibits a binary family over
`𝔽₂^83` (one-element group `G`, `f = d = 1`, `ũ_x = 1`, `c_det = d_K = B = 0`, `M = 1`) with the
fixed-field clearing data (5.9), `ũ_x ∈ Λ[1/2]`, `v₂ ũ_x(0) ≤ B` at every nonzero address, and the
choice (5.10). In it `ũ_0(0) = 1 ≠ 0`, as `base_coordinate_ne_zero` requires; the extra hypothesis
`ũ_0(0) = 0` of `coefficient_transfer_contradiction` is the one that, by Elliot's argument, cannot
hold together with the others (it is what `L'(E/K,1) = 0` would give through Lemma
`ex:arith-base-zero`).
-/

namespace ZInQ.Manuscript.RC.Boolean

open Finset

/-- The trivial pairing of the one-element group with the addresses. -/
def unitPairing (b : ℕ) : Unit → Address b →+ ZMod 2 := fun _ => 0

theorem signEval_unitPairing {R : Type*} [CommRing R] {b : ℕ} (α : Unit → R) (x : Address b) :
    signEval (unitPairing b) α x = α () := by
  simp [signEval, signChar, unitPairing]

/-- `f = d = 1 ∈ 𝒪[G]`, in Laurent coefficients. -/
noncomputable def exampleCoeff : Unit → ℤ → ℤ_[2] := fun _ i => if i = 0 then 1 else 0

/-- `ũ_x = 1` at every address, in power-series coefficients. -/
noncomputable def exampleCoord (b : ℕ) : Address b → ℕ → ℚ_[2] := fun _ k => if k = 0 then 1 else 0

theorem example_fixedFieldClearing :
    FixedFieldClearing (unitPairing 83) exampleCoeff exampleCoeff (exampleCoord 83) 0 0 where
  identity x n := by
    simp only [signEval_unitPairing]
    have h := hasSum_single (f := fun k : ℕ =>
      ((exampleCoeff () (n - k) : ℤ_[2]) : ℚ_[2]) * exampleCoord 83 x k) 0 (fun k hk => by
        simp [exampleCoord, hk])
    simpa [exampleCoord] using h
  f_zero_mem_Lambda i hi := by
    simp [signEval_unitPairing, exampleCoeff, hi.ne]
  fZeroConst_ne_zero := by
    simp [fZeroConst, signEval_unitPairing, exampleCoeff]
  valuation_le_cdet := by
    simp [fZeroConst, signEval_unitPairing, exampleCoeff]
  pole M x i hi := by
    have hi' : i ≠ 0 := by
      have : (0 : ℤ) ≤ (LT 0 M : ℤ) := Int.natCast_nonneg _
      omega
    simp [signEval_unitPairing, exampleCoeff, hi']

theorem example_inLambdaHalf (x : Address 83) : InLambdaHalf (exampleCoord 83 x) :=
  ⟨0, fun k => if k = 0 then 1 else 0, fun k => by
    by_cases hk : k = 0 <;> simp [exampleCoord, hk]⟩

theorem example_bound (x : Address 83) (_hx : x ≠ 0) :
    Padic.addValuation (exampleCoord 83 x 0) ≤ ((0 : ℤ) : WithTop ℤ) := by
  simp [exampleCoord]

theorem example_choice510 : Choice510 0 0 0 1 83 := by
  refine ⟨by norm_num, ?_⟩
  simp [LT]

/-- **Non-vacuity** (kind PROVED): the hypotheses of `coefficient_transfer`, with the bound `B` at
the nonzero addresses, are satisfiable. -/
theorem coefficientTransfer_hypotheses_satisfiable :
    ∃ (b : ℕ) (G : Type) (_ : Fintype G) (ℓ : G → Address b →+ ZMod 2) (f d : G → ℤ → ℤ_[2])
      (u : Address b → ℕ → ℚ_[2]) (cdet dK M : ℕ) (B : ℤ),
      FixedFieldClearing ℓ f d u cdet dK ∧ (∀ x, InLambdaHalf (u x)) ∧
      Choice510 cdet B dK M b ∧
      (∀ x : Address b, x ≠ 0 → Padic.addValuation (u x 0) ≤ (B : WithTop ℤ)) ∧ u 0 0 ≠ 0 :=
  ⟨83, Unit, inferInstance, unitPairing 83, exampleCoeff, exampleCoeff, exampleCoord 83, 0, 0, 1, 0,
    example_fixedFieldClearing, example_inLambdaHalf, example_choice510, example_bound,
    by simp [exampleCoord]⟩

end ZInQ.Manuscript.RC.Boolean
