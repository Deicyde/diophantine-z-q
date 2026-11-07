import ZInQKernel.Syntax.Recipes.Polynomial
import ZInQKernel.Compiler.Universal

/-!
# The specified polynomial at the natural precision circuit

Blueprint: `syntax/literal-polynomial.md` (with `compiler/natural/universal/circuit-node-counts.md`).

The natural precision circuit is `precisionCircuitOf c₃` (the compiler chapter's specialization
of the universal halting circuit at the program literal `c₃`). Its shape, from the compiler
chapter's counts and node statistics, gives `PrecisionShape` (`precisionShape_of`); the node
statistics of the halting circuit enter as the compiler chapter's named finite check
`HaltingNodeCheck`. The program literal `c₃` stays a parameter here (it is the code of the
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

/-- **The shape of the natural precision circuit**, in the form used by the witness accounting,
from the compiler chapter's counts and (given its finite check) node statistics. -/
theorem precisionShape_of (hH : HaltingNodeCheck) (code : ℤ) :
    PrecisionShape (precisionCircuitOf code) code := by
  obtain ⟨hk, hv, -, -, -⟩ := precisionCircuitOf_counts code
  obtain ⟨-, -, -, hadd, hmul, hcall, hconst⟩ := precisionCircuitOf_nodeStats hH code
  refine ⟨hk, hv.le, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨rest, -, h⟩ := precisionCircuitOf_explicitVars code
    rw [h, List.countP_append]
    have : List.countP (fun v => decide (IsInputVar 5 v))
        [((0 : ℕ), VarKind.input), (1, .input), (2, .input), (3, .input), (4, .input),
          (5, .witness), (6, .witness), (7, .witness), (8, .witness)] = 5 := by decide
    rw [this]
    exact Nat.le_add_right _ _
  · rw [← countKind_add, hadd]
  · rw [← countKind_mul, hmul]
  · rw [← countKind_call, hcall]
  · intro c hc
    obtain ⟨hm, hn⟩ := mem_filterMap_nontrivialConst hc
    rw [hconst] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    obtain ⟨h0, h1, h2⟩ := hn
    omega

section Literal

variable (c3 : ℤ)

/-- **The specified polynomial** `P_* ∈ ℤ[X_0, …, X_{292890231904}]` at the natural precision
circuit with program literal `c₃`. -/
noncomputable def specPstar : MvPolynomial (Fin 292890231905) ℤ := Pstar (precisionCircuitOf c3) c3

/-- `P_*` is `[[integers]]` in the variables `X_0, …, X_{292890231904}`: same coefficients, no
larger total degree. -/
theorem specPstar_spec (hH : HaltingNodeCheck) :
    MvPolynomial.rename Fin.val (specPstar c3) = PstarNat (precisionCircuitOf c3) c3 ∧
      (∀ d, (specPstar c3).coeff d =
        (PstarNat (precisionCircuitOf c3) c3).coeff (d.mapDomain Fin.val)) ∧
      (specPstar c3).totalDegree ≤ (PstarNat (precisionCircuitOf c3) c3).totalDegree ∧
      ∀ v : Fin 292890231905 → ℚ, MvPolynomial.eval₂ (Int.castRingHom ℚ) v (specPstar c3) =
        ev (extendFin v) (PstarNat (precisionCircuitOf c3) c3) :=
  Pstar_spec _ _ (precisionShape_of hH c3)

/-- **The rational zero projection of `P_*`.** -/
theorem specPstar_zero_projection (hH : HaltingNodeCheck) (q : ℚ) :
    (∃ w : Fin 292890231904 → ℚ,
        MvPolynomial.eval₂ (Int.castRingHom ℚ) (Fin.cons q w) (specPstar c3) = 0) ↔
      ∃ M : Fin 5 → ℚ, (valueExPoly specConstructors FixedConst.cstar.value FixedConst.ell.value
        FixedConst.T.value c3 (precisionCircuitOf c3)).Rel (fun i => Fin.append M ![q] (Fin.cast
          (valueExPoly_params specConstructors FixedConst.cstar.value FixedConst.ell.value
            FixedConst.T.value c3 (precisionCircuitOf c3)) i)) :=
  Pstar_zero_projection _ _ (precisionShape_of hH c3) q

end Literal

end ZInQ.Syntax
