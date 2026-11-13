import ZInQKernel.Size.Majorants.Cutoff
import ZInQKernel.Size.Majorants.Towers

/-!
# Degree and coefficient bounds for the specified polynomial

Blueprint: `size/majorants/degree-coefficient-bound.md` and `size/syntax-bounds.md`.

`P_* = specPstar c₃ ∈ ℤ[X_0, …, X_{292890231904}]` (syntax-recipes) is `[[integers]]` read in
`Fin 292890231905` variables. Under the catalogue bound, `B = T + 1` is admissible
(`admissible_cutoff`), so the recipe heights give `Maj_{T+1}(256, [[integers]])`: degree at most
`(T+1)^2048` and norm at most `2^((T+1)^2048)`; `P_*` has the coefficients of `[[integers]]`
and no larger degree (`specPstar_spec`). With `T < 2^2^2^9013` (`T_lt`) the tower comparison
gives the bounds of the target.

Besides the catalogue bound, the statements take the two inputs of the compiler chapter that
the specified polynomial depends on: the bound `NodeCheck.HaltingAddMulBound` on the addition
and multiplication counts of the universal halting circuit (which gives the shape of the natural
precision circuit and hence the witness accounting and the constraint count of the precision
recipe),
and the size `|c₃| < 2^(2^24)` of the program literal.
-/

namespace ZInQ.Size

open MvPolynomial ZInQ.Syntax ZInQ.Compiler.Universal

/-- The majorant at height `256`: degree at most `B^2048` and norm at most `2^(B^2048)`. -/
theorem maj_two_fifty_six {σ : Type*} {B : ℕ} {P : MvPolynomial σ ℤ} (h : Maj B 256 P) :
    P.totalDegree ≤ B ^ 2048 ∧ l1 P ≤ 2 ^ B ^ 2048 := by
  rw [maj_iff_of_ne_zero (by norm_num), show 8 * 256 = 2048 from rfl] at h
  exact h

/-- `[[integers]]` satisfies the majorant at height `256` for `B = T + 1`. -/
theorem PstarNat_maj (hCAT : CatalogueBound8) (hB : Compiler.NodeCheck.HaltingAddMulBound) {c3 : ℤ}
    (hc3 : c3.natAbs < 2 ^ 2 ^ 24) :
    Maj (Syntax.T + 1) 256 (PstarNat (precisionCircuitOf c3) c3) :=
  integers_maj (admissible_cutoff hCAT hc3) (precisionShape_of hB c3)

/-- **Degree and coefficient bounds for the specified polynomial.** Under the catalogue bound,
`deg P_* ≤ (T+1)^2048` and `|[X^α] P_*| ≤ ‖P_*‖₁ ≤ 2^((T+1)^2048)` for every monomial `X^α`. -/
theorem Pstar_degree_coeff (hCAT : CatalogueBound8) (hB : Compiler.NodeCheck.HaltingAddMulBound) {c3 : ℤ}
    (hc3 : c3.natAbs < 2 ^ 2 ^ 24) :
    (specPstar c3).totalDegree ≤ (Syntax.T + 1) ^ 2048 ∧
      l1 (specPstar c3) ≤ 2 ^ (Syntax.T + 1) ^ 2048 ∧
      ∀ m, ((specPstar c3).coeff m).natAbs ≤ l1 (specPstar c3) := by
  obtain ⟨hdeg, hl1⟩ := maj_two_fifty_six (PstarNat_maj hCAT hB hc3)
  obtain ⟨hren, -, hdeg', -⟩ := specPstar_spec c3 hB
  have hl1' : l1 (specPstar c3) = l1 (PstarNat (precisionCircuitOf c3) c3) := by
    rw [← hren, l1_rename_of_injective Fin.val_injective]
  refine ⟨hdeg'.trans hdeg, hl1'.trans_le hl1, fun m => natAbs_coeff_le_l1 _ m⟩

/-- **Variable, degree and coefficient bounds of the specified polynomial.** Under the
catalogue bound, `P_* ∈ ℤ[X_0, …, X_{292890231904}]` (the variable count is its type: the input
`X_0` and `292890231904` witnesses, by the witness accounting) has
`deg P_* ≤ (T+1)^2048 < 2↑↑7` and `|[X^α] P_*| ≤ 2^((T+1)^2048) < 2↑↑8`. -/
theorem Pstar_size (hCAT : CatalogueBound8) (hB : Compiler.NodeCheck.HaltingAddMulBound) {c3 : ℤ}
    (hc3 : c3.natAbs < 2 ^ 2 ^ 24) :
    ((specPstar c3).totalDegree ≤ (Syntax.T + 1) ^ 2048 ∧
        (Syntax.T + 1) ^ 2048 < hyperoperation 4 2 7) ∧
      (∀ m : Fin 292890231905 →₀ ℕ, ((specPstar c3).coeff m).natAbs ≤ 2 ^ (Syntax.T + 1) ^ 2048) ∧
      2 ^ (Syntax.T + 1) ^ 2048 < hyperoperation 4 2 8 := by
  obtain ⟨hdeg, hl1, hcoeff⟩ := Pstar_degree_coeff hCAT hB hc3
  exact ⟨⟨hdeg, degree_lt_tower_seven _ (T_lt hCAT)⟩, fun m => (hcoeff m).trans hl1,
    coefficient_lt_tower_eight _ (T_lt hCAT)⟩

/-- The degree and coefficient conjuncts of the target `FrozenTarget` for `P_*`. -/
theorem Pstar_target_bounds (hCAT : CatalogueBound8) (hB : Compiler.NodeCheck.HaltingAddMulBound) {c3 : ℤ}
    (hc3 : c3.natAbs < 2 ^ 2 ^ 24) :
    (specPstar c3).totalDegree < hyperoperation 4 2 7 ∧
      ∀ m : Fin 292890231905 →₀ ℕ, ((specPstar c3).coeff m).natAbs < hyperoperation 4 2 8 := by
  obtain ⟨⟨hdeg, hdeg7⟩, hcoeff, hcoeff8⟩ := Pstar_size hCAT hB hc3
  exact ⟨hdeg.trans_lt hdeg7, fun m => (hcoeff m).trans_lt hcoeff8⟩

end ZInQ.Size
