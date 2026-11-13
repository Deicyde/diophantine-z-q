import ZInQKernel.Compiler.NodeCheck.Check
import ZInQKernel.Compiler.NodeCheck.Consts

/-!
# The node check reduced to the addition and multiplication counts

Three of the five items of `HaltingNodeCheck` are proved without evaluating the construction:
the variable-node count (`haltingCircuit_varNodes`), the constant-node count
(`haltingCircuit_constNodes`) and the constant list (`haltingCircuit_constList`). What remains
is the named finite check `HaltingAddMulCheck`: the numbers of addition and multiplication
nodes, which depend on every hash-consing hit of the construction.
-/

namespace ZInQ.Compiler.NodeCheck

open Natural Universal

/-- **FINITE CHECK** (input of milestone 1, to be replaced by a kernel certificate): the
addition and multiplication counts of the universal halting circuit, the part of
`HaltingNodeCheck` not proved symbolically. -/
def HaltingAddMulCheck : Prop :=
  countKind .add haltingCircuit.nodes = 125307 ∧ countKind .mul haltingCircuit.nodes = 98361

noncomputable instance : Decidable HaltingAddMulCheck := by unfold HaltingAddMulCheck; infer_instance

/-- `HaltingNodeCheck` from its addition and multiplication counts. -/
theorem haltingNodeCheck_of_addMul (h : HaltingAddMulCheck) : HaltingNodeCheck :=
  ⟨haltingCircuit_varNodes, haltingCircuit_constNodes, h.1, h.2, haltingCircuit_constList⟩

/-- The Boolean check of the addition and multiplication counts, on the reversed node list. -/
def addMulCheck (l : List NatNode) : Bool :=
  match countGo l 0 0 0 0 [] with
  | (_, _, a, m, _) => a.beq 125307 && m.beq 98361

/-- **The Boolean addition and multiplication check**: the fast builder run on `𝒰`. -/
def haltingAddMulCheckB : Bool := addMulCheck (fastNodesRev interpreter 204 2)

theorem addMulCheck_sound {l L : List NatNode} (hL : L = l.reverse) (h : addMulCheck l = true) :
    countKind .add L = 125307 ∧ countKind .mul L = 98361 := by
  unfold addMulCheck at h
  rw [countGo_eq] at h
  simp only [Bool.and_eq_true, Nat.beq_eq, Nat.zero_add] at h
  subst hL
  rw [countKind_reverse, countKind_reverse]
  exact h

/-- **Soundness of the Boolean addition and multiplication check.** -/
theorem haltingAddMulCheck_of_checkB (h : haltingAddMulCheckB = true) : HaltingAddMulCheck :=
  addMulCheck_sound (L := haltingCircuit.nodes) (compiled_nodes interpreter 204 2) h

end ZInQ.Compiler.NodeCheck
