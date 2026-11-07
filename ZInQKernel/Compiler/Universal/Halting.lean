import ZInQKernel.Compiler.Universal.Shape
import ZInQKernel.Compiler.Universal.Grows

/-!
# The universal halting circuit

The universal halting circuit `ℋ = 𝒞_{𝒰,2}` is the compiled circuit of the packed-history
construction of the universal interpreter with `r = 204` registers and `k = 2` inputs
`e = X_0`, `n = X_1`.

1. Its explicit variables are `X_0, X_1` followed by the `54,047` fresh witnesses of the
   construction, and its node list begins with the variable nodes of `X_0` and `X_1`.
2. Counts: `54,049` explicit variables, `15,845` calls of the power template (blocks of `79`),
   variable count `54,049 + 79 · 15,845 = 1,305,804`; `1,603` mask, `1,226` bitAnd, `3,678`
   orthogonal, `5,281` binomial macros and `10,770` strict inequalities. It is well scoped.
3. Its natural zeros with inputs `(e, n)` are exactly the inputs accepted by `𝒰`.

The counts are the counting statement of the packed construction (`Packed.packed_counts`)
at `(k, r, m, s) = (2, 204, 1399, 1022)`, the shape of `𝒰`; nothing is evaluated.

(Blueprint: `compiler/natural/universal/halting-polynomial.md`,
`halting-circuit-counts.md`, `halting-polynomial-semantics.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Universal

open RM Natural Packed

/-- **The universal halting circuit** `ℋ = 𝒞_{𝒰,2}`. -/
def haltingCircuit : NatCircuit := compiled interpreter 204 2

theorem haltingCircuit_inputCount : haltingCircuit.inputCount = 2 := rfl

/-- The explicit variables of `ℋ` are the inputs `X_0, X_1` followed by witnesses. -/
theorem haltingCircuit_explicitVars_eq' :
    ∃ rest, haltingCircuit.explicitVars = (0, .input) :: (1, .input) :: rest ∧
      ∀ v ∈ rest, v.2 = .witness := by
  obtain ⟨rest, h, hw⟩ := (compiled_prefix interpreter 204 2).1
  exact ⟨rest, h, hw⟩

theorem haltingCircuit_explicitVars_eq :
    ∃ rest, haltingCircuit.explicitVars = (0, .input) :: (1, .input) :: rest := by
  obtain ⟨rest, h, -⟩ := haltingCircuit_explicitVars_eq'
  exact ⟨rest, h⟩

/-- The node list of `ℋ` begins with the variable nodes of `X_0` and `X_1`. -/
theorem haltingCircuit_nodes_eq : ∃ rest, haltingCircuit.nodes = .var 0 :: .var 1 :: rest := by
  obtain ⟨rest, h⟩ := (compiled_prefix interpreter 204 2).2.1
  exact ⟨rest, h.symm⟩

/-- The nodes of `ℋ` other than call nodes are pairwise distinct (hash-consing). -/
theorem haltingCircuit_nonCall_nodup : (nonCall haltingCircuit.nodes).Nodup :=
  (compiled_prefix interpreter 204 2).2.2.1

/-- The constants of `ℋ` are among `0, 1, 2, 4, -1, 1399`. -/
theorem haltingCircuit_consts {c : ℤ} (h : NatNode.const c ∈ haltingCircuit.nodes) :
    c ∈ ({0, 1, 2, 4, -1, 1399} : Set ℤ) := by
  have := (compiled_prefix interpreter 204 2).2.2.2 c h
  rwa [interpreter_length] at this

/-- **Counts of the universal halting circuit**: `54,049` explicit variables, `15,845` calls
(blocks), variable count `1,305,804`, and well-scopedness. -/
theorem haltingCircuit_counts :
    haltingCircuit.inputCount = 2 ∧ haltingCircuit.explicitVars.length = 54049 ∧
    haltingCircuit.blocks.length = 15845 ∧
    haltingCircuit.nodes.countP NatNode.isCall = 15845 ∧
    haltingCircuit.varCount = 1305804 ∧ haltingCircuit.WellScoped := by
  obtain ⟨-, -, -, -, -, -, -, hb, hv, hn⟩ := packed_counts interpreter 204 2
  rw [interpreter_length, interpreter_subCount] at hb hv hn
  refine ⟨rfl, hv, hb, ?_, hn, compiled_wellScoped _ _ _⟩
  rw [← blocks_length]
  exact hb

/-- A natural zero of `ℋ` with inputs `(e, n)` has `1,305,802` witness coordinates. -/
theorem haltingCircuit_witnessCount :
    haltingCircuit.varCount - haltingCircuit.inputCount = 1305802 := by
  rw [haltingCircuit_counts.2.2.2.2.1, haltingCircuit_inputCount]

/-- The macro counts of the construction of `ℋ`: `1,603` masks, `1,226` bitAnds, `3,678`
orthogonals, `5,281` binomials, `5,281` odd gadgets, `10,770` strict inequalities and `15,845`
power macros. -/
theorem haltingCircuit_macroCounts :
    let L := (construction interpreter 204 2 (State.init 2)).2.log
    L.count .mask = 1603 ∧ L.count .bitAnd = 1226 ∧ L.count .orthogonal = 3678 ∧
    L.count .binomial = 5281 ∧ L.count .odd = 5281 ∧ L.count .lt = 10770 ∧
    L.count .power = 15845 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := packed_counts interpreter 204 2
  simp only [interpreter_length, interpreter_subCount] at h1 h2 h3 h4 h5 h6 h7
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **The universal halting circuit accepts what the interpreter accepts.** For all
`e, n ∈ ℕ`, `ℋ` has a natural zero with inputs `(e, n)` iff `𝒰` accepts `(e, n)`. -/
theorem haltingCircuit_natRel_iff_accepts (e n : ℕ) :
    haltingCircuit.NatRel powerTemplate ![e, n] ↔ interpreter.Accepts ![e, n] :=
  compiled_natRel_iff interpreter 204 2 interpreter_valid (by norm_num) (by norm_num) _

end ZInQ.Compiler.Universal
