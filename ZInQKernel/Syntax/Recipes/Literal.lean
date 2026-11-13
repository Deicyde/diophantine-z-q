import ZInQKernel.Syntax.Recipes.Polynomial
import ZInQKernel.Compiler.Universal

/-!
# The specified polynomial at the natural precision circuit

Blueprint: `syntax/literal-polynomial.md` (with `compiler/natural/universal/circuit-node-counts.md`).

The natural precision circuit is `precisionCircuitOf c₃` (the compiler chapter's specialization
of the universal halting circuit at the program literal `c₃`). Its shape, from the compiler
chapter's counts and node statistics, gives `PrecisionShape` (`precisionShape_of`); the node
statistics of the halting circuit enter only through the upper bounds on its addition and
multiplication counts, `NodeCheck.HaltingAddMulBound`. The program literal `c₃` stays a parameter here (it is the code of the
wrapper program, built by the compiler chapter); no property of it is needed for the variable
bound, since `c₃` is only ever the fourth entry of the constant table.
-/

namespace ZInQ.Syntax

open ZInQ.Compiler.Natural ZInQ.Compiler.Universal

theorem countKind_add (l : List NatNode) : countKind .add l = l.countP NatNode.isAdd := by
  unfold countKind
  congr 1
  funext n
  cases n <;> rfl

theorem countKind_mul (l : List NatNode) : countKind .mul l = l.countP NatNode.isMul := by
  unfold countKind
  congr 1
  funext n
  cases n <;> rfl

theorem mem_filterMap_nontrivialConst {l : List NatNode} {c : ℤ}
    (h : c ∈ l.filterMap nontrivialConst) : c ∈ constList l ∧ IsNontrivial c := by
  obtain ⟨n, hn, hc⟩ := List.mem_filterMap.1 h
  cases n with
  | const d =>
    simp only [nontrivialConst] at hc
    split_ifs at hc with hd
    cases hc
    exact ⟨List.mem_filterMap.2 ⟨_, hn, rfl⟩, hd⟩
  | var _ => cases hc
  | add _ _ => cases hc
  | mul _ _ => cases hc
  | call _ _ _ _ => cases hc

/-- A nontrivial constant of the precision circuit is `code`, `2`, `4` or `1399`; this needs no
node check. -/
theorem precisionCircuitOf_nontrivialConst {code c : ℤ}
    (hc : c ∈ (precisionCircuitOf code).nodes.filterMap nontrivialConst) :
    c = code ∨ c = 2 ∨ c = 4 ∨ c = 1399 := by
  obtain ⟨n, hn, hnc⟩ := List.mem_filterMap.1 hc
  cases n with
  | const d =>
    simp only [nontrivialConst] at hnc
    split_ifs at hnc with hd
    cases hnc
    have hm := precisionCircuitOf_consts code hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    obtain ⟨h0, h1, h2⟩ := hd
    omega
  | var _ => cases hnc
  | add _ _ => cases hnc
  | mul _ _ => cases hnc
  | call _ _ _ _ => cases hnc

/-- **The shape of the natural precision circuit**, in the form used by the witness accounting,
from the compiler chapter's counts and the addition and multiplication bound of the halting
circuit. -/
theorem precisionShape_of (hB : Compiler.NodeCheck.HaltingAddMulBound) (code : ℤ) :
    PrecisionShape (precisionCircuitOf code) code := by
  obtain ⟨hk, hv, -, -, -⟩ := precisionCircuitOf_counts code
  obtain ⟨hadd, hmul⟩ := precisionCircuitOf_addMulBound hB code
  refine ⟨hk, hv.le, ?_, ?_, ?_, ?_, fun c hc => precisionCircuitOf_nontrivialConst hc⟩
  · obtain ⟨rest, -, -, h⟩ := precisionCircuitOf_explicitVars code
    rw [h, List.countP_append]
    have : List.countP (fun v => decide (IsInputVar 5 v))
        [((0 : ℕ), VarKind.input), (1, .input), (2, .input), (3, .input), (4, .input),
          (5, .witness), (6, .witness), (7, .witness), (8, .witness)] = 5 := by decide
    rw [this]
    exact Nat.le_add_right _ _
  · rw [← countKind_add]; exact hadd
  · rw [← countKind_mul]; exact hmul
  · rw [← countKind_call, precisionCircuitOf_countKind_call]

section Literal

variable (c3 : ℤ)

/-- **The specified polynomial** `P_* ∈ ℤ[X_0, …, X_{292890231904}]` at the natural precision
circuit with program literal `c₃`. -/
noncomputable def specPstar : MvPolynomial (Fin 292890231905) ℤ := Pstar (precisionCircuitOf c3) c3

/-- `P_*` is `[[integers]]` in the variables `X_0, …, X_{292890231904}`: same coefficients, no
larger total degree. -/
theorem specPstar_spec (hB : Compiler.NodeCheck.HaltingAddMulBound) :
    MvPolynomial.rename Fin.val (specPstar c3) = PstarNat (precisionCircuitOf c3) c3 ∧
      (∀ d, (specPstar c3).coeff d =
        (PstarNat (precisionCircuitOf c3) c3).coeff (d.mapDomain Fin.val)) ∧
      (specPstar c3).totalDegree ≤ (PstarNat (precisionCircuitOf c3) c3).totalDegree ∧
      ∀ v : Fin 292890231905 → ℚ, MvPolynomial.eval₂ (Int.castRingHom ℚ) v (specPstar c3) =
        ev (extendFin v) (PstarNat (precisionCircuitOf c3) c3) :=
  Pstar_spec _ _ (precisionShape_of hB c3)

/-- **The rational zero projection of `P_*`.** -/
theorem specPstar_zero_projection (hB : Compiler.NodeCheck.HaltingAddMulBound) (q : ℚ) :
    (∃ w : Fin 292890231904 → ℚ,
        MvPolynomial.eval₂ (Int.castRingHom ℚ) (Fin.cons q w) (specPstar c3) = 0) ↔
      ∃ M : Fin 5 → ℚ, (valueExPoly specConstructors FixedConst.cstar.value FixedConst.ell.value
        FixedConst.T.value c3 (precisionCircuitOf c3)).Rel (fun i => Fin.append M ![q] (Fin.cast
          (valueExPoly_params specConstructors FixedConst.cstar.value FixedConst.ell.value
            FixedConst.T.value c3 (precisionCircuitOf c3)) i)) :=
  Pstar_zero_projection _ _ (precisionShape_of hB c3) q

end Literal

end ZInQ.Syntax
