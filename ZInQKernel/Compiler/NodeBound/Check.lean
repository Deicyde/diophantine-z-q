import ZInQKernel.Compiler.NodeBound.Top
import ZInQKernel.Compiler.Universal.Halting

/-!
# The addition and multiplication bound of the halting circuit

The bounds `addBound` and `mulBound` of `compiled_bound` at the universal interpreter `𝒰`
(`1,399` instructions, `1,022` of them sub instructions, `204` registers, `2` inputs) are
`125,307` and `98,361`. The program-dependent parts (`cost6`, `cost7A`, `cost7M`, `nC7`) are
small kernel computations: the symbolic handle lists are read from buckets filled in one pass
over the program (`NodeCheck.incHandles_eq`, `decHandles_eq`, `inHandles_eq`).
-/

namespace ZInQ.Compiler.NodeBound

open Natural Universal RM

/-- The buckets of the symbolic summands of `A_j`. -/
def incB (p : Program) : NodeCheck.NTrie (List ℕ) :=
  NodeCheck.buckets (NodeCheck.pairsGo 0 NodeCheck.incPairF 0 p (sCodes p.length))

/-- The buckets of the symbolic summands of `C_j`. -/
def decB (p : Program) : NodeCheck.NTrie (List ℕ) :=
  NodeCheck.buckets (NodeCheck.pairsGo 0 (NodeCheck.decPairF 0 (NodeCheck.vwTrie (vwCodes p))) 0 p
    (sCodes p.length))

/-- The buckets of the symbolic summands of `I_i`. -/
def inB (p : Program) : NodeCheck.NTrie (List ℕ) :=
  NodeCheck.buckets (NodeCheck.pairsGo 0 (NodeCheck.inPairF 0 (NodeCheck.vwTrie (vwCodes p))) 0 p
    (sCodes p.length))

theorem symInc_eq (p : Program) : symInc p = fun j => NodeCheck.bucketGet (incB p) j := by
  funext j; exact NodeCheck.incHandles_eq ..

theorem symDec_eq (p : Program) : symDec p = fun j => NodeCheck.bucketGet (decB p) j := by
  funext j; exact NodeCheck.decHandles_eq ..

theorem symIn_eq (p : Program) : symIn p = fun i => NodeCheck.bucketGet (inB p) i := by
  funext i; exact NodeCheck.inHandles_eq ..

theorem cost6_interpreter : cost6 interpreter (203 + 1) = 1602 := by
  unfold cost6
  rw [symInc_eq, symDec_eq]
  decide +kernel

theorem nC7_interpreter : nC7 (symIn interpreter) (List.range interpreter.length) = 12 := by
  rw [symIn_eq]
  decide +kernel

theorem cost7A_interpreter :
    cost7A (symIn interpreter) (decPos 0 interpreter) (List.range interpreter.length) false =
      2384 := by
  rw [symIn_eq]
  decide +kernel

theorem cost7M_interpreter :
    cost7M (symIn interpreter) (singles interpreter (203 + 1)) (List.range interpreter.length)
      false =
      1248 := by
  rw [symIn_eq, singles, symInc_eq]
  decide +kernel

theorem addBound_interpreter : addBound interpreter 203 2 = 125307 := by
  rw [addBound, itemsA, formA, formN, cost6_interpreter, cost7A_interpreter, interpreter_subCount,
    interpreter_length]

theorem mulBound_interpreter : mulBound interpreter 203 2 = 98361 := by
  rw [mulBound, itemsM, formM, formN, cost7M_interpreter, nC7_interpreter, interpreter_subCount,
    interpreter_length]

end ZInQ.Compiler.NodeBound

namespace ZInQ.Compiler.NodeCheck

open Natural Universal NodeBound

/-- **The addition and multiplication bound of the universal halting circuit**, proved in the
kernel: at most `125,307` addition and `98,361` multiplication nodes. -/
theorem haltingAddMulBound : HaltingAddMulBound := by
  have h := compiled_bound interpreter 203 2 (by rw [interpreter_length]; omega)
  rw [addBound_interpreter, mulBound_interpreter] at h
  exact h

end ZInQ.Compiler.NodeCheck
