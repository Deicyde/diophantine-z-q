import ZInQKernel.Compiler.Universal.WrapperSize
import ZInQKernel.Compiler.Universal.PrecisionCircuit
import ZInQKernel.Compiler.Precision
import ZInQKernel.Compiler.Interpreter.Correct

/-!
# The program literal and the natural precision polynomial

1. The program literal `c₃ = code(𝒲)` satisfies `1399 < c₃ < 2^14400019 < 2^(2^24)`; its value
   is never computed (`c₃` is an irreducible definition, and only these bounds are used).
2. The five-input natural precision circuit `𝒩` is the specialization of the universal halting
   circuit at `c₃`; its shape and semantics are those of `precisionCircuitOf` at `c₃`.
3. Equation (C.4): `Z_𝒩(c) ↔ accepts(c)` for `c ∈ ℕ⁵`, from the semantics of `ℋ`, the codes of
   primitive programs and the correctness of the interpreter and of the wrapper.

(Blueprint: `compiler/natural/universal/wrapper-code-size.md`, `precision-circuit.md`,
`circuit-node-counts.md`, `compiler/natural/natural-polynomial-semantics.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Universal

open RM Natural IR

/-- **The program literal** `c₃ = code(𝒲)`, the code of the wrapper. It is never evaluated. -/
irreducible_def c3 : ℕ := code wrapper

/-- **Size of the program literal**: `c₃ < 2^14400019`. -/
theorem c3_lt : c3 < 2 ^ 14400019 := by
  rw [c3_def]; exact code_lt_of_small wrapper_small

/-- `c₃ < 2^(2^24)`, the bound used by the size chapter. -/
theorem c3_lt' : c3 < 2 ^ 2 ^ 24 := c3_lt.trans two_pow_14400019_lt

/-- `1399 < c₃`, used by the shape of the natural precision circuit. -/
theorem c3_gt : 1399 < c3 := by
  rw [c3_def]; exact code_gt_of_small wrapper_valid wrapper_small

/-- **The five-input natural precision circuit** `𝒩`: the universal halting circuit specialized
at the program literal `c₃`. -/
def precisionCircuit : NatCircuit := precisionCircuitOf c3

theorem precisionCircuit_eq : precisionCircuit = precisionCircuitOf c3 := rfl

/-- `[[𝒩]] = θ([[ℋ]])² + Σ_{i<4} π_i²` with `θ : X_0 ↦ c₃, X_1 ↦ X_5, X_i ↦ X_{i+7}`. -/
theorem precisionCircuit_poly (T : Syntax.ExPoly) :
    precisionCircuit.poly T =
      MvPolynomial.bind₁ (theta c3) (haltingCircuit.poly T) ^ 2 + ∑ i : Fin 4, pairPoly i ^ 2 := by
  rw [precisionCircuit_eq]; exact precisionCircuitOf_poly c3 T

/-- **The precision circuit is a specialization**: `Z_𝒩(c) ↔ Z_ℋ(c₃, enc₅(c))`. -/
theorem precisionCircuit_natRel_iff (T : Syntax.ExPoly) (c : Fin 5 → ℕ) :
    precisionCircuit.NatRel T c ↔
      haltingCircuit.NatRel T ![c3, CantorDecoder.encode5 (c 0) (c 1) (c 2) (c 3) (c 4)] :=
  precisionCircuitOf_natRel_iff c3 T c

theorem precisionCircuit_wellScoped : precisionCircuit.WellScoped := by
  rw [precisionCircuit_eq]; exact precisionCircuitOf_wellScoped c3

/-- **Shape of the natural precision circuit**, items 1–2: `5` inputs, `54,056` explicit
variables, `15,845` calls, variable count `1,305,811`, `1,305,806` witness coordinates. -/
theorem precisionCircuit_counts :
    precisionCircuit.inputCount = 5 ∧ precisionCircuit.explicitVars.length = 54056 ∧
    precisionCircuit.blocks.length = 15845 ∧ precisionCircuit.varCount = 1305811 ∧
    precisionCircuit.varCount - precisionCircuit.inputCount = 1305806 := by
  rw [precisionCircuit_eq]; exact precisionCircuitOf_counts c3

/-- **Shape of the natural precision circuit**, item 3, from the node check of `ℋ`. -/
theorem precisionCircuit_nodeStats (hN : HaltingNodeCheck) :
    precisionCircuit.nodes.length = 293620 ∧
    countKind .var precisionCircuit.nodes = 54056 ∧
    countKind .const precisionCircuit.nodes = 10 ∧
    countKind .add precisionCircuit.nodes = 125327 ∧
    countKind .mul precisionCircuit.nodes = 98382 ∧
    countKind .call precisionCircuit.nodes = 15845 ∧
    constList precisionCircuit.nodes = [(c3 : ℤ), 0, 1, 2, 4, 1399, -1, 1, 2, -1] := by
  rw [precisionCircuit_eq]; exact precisionCircuitOf_nodeStats hN c3

/-- **Shape of the natural precision circuit**, item 3, the addition and multiplication bounds,
from the bound of `ℋ`. -/
theorem precisionCircuit_addMulBound (hB : NodeCheck.HaltingAddMulBound) :
    countKind .add precisionCircuit.nodes ≤ 125327 ∧
    countKind .mul precisionCircuit.nodes ≤ 98382 := by
  rw [precisionCircuit_eq]; exact precisionCircuitOf_addMulBound hB c3

/-- **Shape of the natural precision circuit**, item 4 (without the node check): every constant
is among `0, 1, -1, c₃, 2, 4, 1399`, and `c₃, 2, 4, 1399` are distinct. -/
theorem precisionCircuit_consts :
    (∀ c, NatNode.const c ∈ precisionCircuit.nodes →
      c ∈ ({(c3 : ℤ), 0, 1, 2, 4, 1399, -1} : Set ℤ)) ∧ [(c3 : ℤ), 2, 4, 1399].Nodup := by
  rw [precisionCircuit_eq]
  refine ⟨fun c h => precisionCircuitOf_consts c3 h, ?_⟩
  have := c3_gt
  refine List.nodup_cons.2 ⟨?_, by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  omega

/-- The universal halting circuit at the wrapper's code: `Z_ℋ(c₃, n) ↔ 𝒲` halts on `n`, given the
correctness of the interpreter. -/
theorem haltingCircuit_c3_iff (hU : ∀ e n, interpreter.Accepts ![e, n] ↔ halts e n) (n : ℕ) :
    haltingCircuit.NatRel powerTemplate ![c3, n] ↔ wrapper.HaltsOn ![n] := by
  rw [haltingCircuit_natRel_iff_of hU, c3_def]
  exact halts_code_iff wrapper _ wrapper_valid n

/-- **Semantics of the universal halting circuit**: `Z_ℋ(e, n) ↔ halts(e, n)`: the compiled
circuit of the valid program `𝒰` accepts what `𝒰` accepts, and `𝒰` accepts `(e, n)` iff the
program numbered `e` halts on `n` (`interpreter_accepts_iff`). -/
theorem haltingCircuit_natRel_iff (e n : ℕ) :
    haltingCircuit.NatRel powerTemplate ![e, n] ↔ halts e n :=
  haltingCircuit_natRel_iff_of interpreter_accepts_iff e n

end ZInQ.Compiler.Universal

namespace ZInQ.Compiler

open Universal Natural

/-- **Semantics of the natural precision polynomial** (equation (C.4)), from the correctness of
the universal interpreter and of the wrapper. -/
theorem natural_polynomial_semantics_of
    (hU : ∀ e n, interpreter.Accepts ![e, n] ↔ halts e n)
    (hW : ∀ c : Fin 5 → ℕ,
      IR.wrapper.HaltsOn ![CantorDecoder.encode5 (c 0) (c 1) (c 2) (c 3) (c 4)] ↔
        Precision.accepts c)
    (c : Fin 5 → ℕ) :
    precisionCircuit.NatRel powerTemplate c ↔ Precision.accepts c := by
  rw [precisionCircuit_natRel_iff, haltingCircuit_c3_iff hU, hW]

/-- **Semantics of the natural precision polynomial** (equation (C.4)): for every `c ∈ ℕ⁵`, the
natural precision circuit has a natural zero with inputs `c` (some natural values of its other
`1,305,806` variables) iff `c` is accepted by the precision relation.

It is `natural_polynomial_semantics_of` applied to the correctness of the interpreter
(`interpreter_accepts_iff`) and of the wrapper (`IR.wrapper_halts_encode`). -/
theorem natural_polynomial_semantics (c : Fin 5 → ℕ) :
    precisionCircuit.NatRel powerTemplate c ↔ Precision.accepts c :=
  natural_polynomial_semantics_of interpreter_accepts_iff IR.wrapper_halts_encode c

theorem natRel_iff_witnessCount (C : NatCircuit) (T : Syntax.ExPoly) {m : ℕ}
    (hm : C.varCount - C.inputCount = m) (c : Fin C.inputCount → ℕ) :
    C.NatRel T c ↔ ∃ z : Fin m → ℕ,
      MvPolynomial.eval (fun i => (NatCircuit.natPoint C.inputCount m c z i : ℤ)) (C.poly T) = 0 := by
  subst hm; rfl

/-- The natural relation of the precision circuit with its `1,305,806` witness coordinates
written out. -/
theorem precisionCircuit_natRel_iff_witnesses (T : Syntax.ExPoly) (c : Fin 5 → ℕ) :
    precisionCircuit.NatRel T c ↔ ∃ z : Fin 1305806 → ℕ,
      MvPolynomial.eval (fun i => (NatCircuit.natPoint 5 1305806 c z i : ℤ))
        (precisionCircuit.poly T) = 0 :=
  natRel_iff_witnessCount precisionCircuit T precisionCircuit_counts.2.2.2.2 c

/-- **Equation (C.4)** in the form of the article: some `z ∈ ℕ^1305806` makes `[[𝒩]](c, z)`
vanish iff `c` is accepted. -/
theorem natural_polynomial_semantics' (c : Fin 5 → ℕ) :
    (∃ z : Fin 1305806 → ℕ,
      MvPolynomial.eval (fun i => (NatCircuit.natPoint 5 1305806 c z i : ℤ))
        (precisionCircuit.poly powerTemplate) = 0) ↔ Precision.accepts c :=
  (precisionCircuit_natRel_iff_witnesses powerTemplate c).symm.trans
    (natural_polynomial_semantics c)

end ZInQ.Compiler
