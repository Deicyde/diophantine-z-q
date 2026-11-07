import ZInQKernel.Compiler.Universal.Halting

/-!
# Node statistics of the halting circuit and the power template

1. The node list of the universal halting circuit `ℋ` has `293,568` nodes: `54,049` variable
   nodes, `6` constant nodes with values `0, 1, 2, 4, 1399, -1` in node order, `125,307`
   additions, `98,361` multiplications and `15,845` calls. Its first two nodes are the variable
   nodes of `X_0` and `X_1`.
2. The node list of the power template `𝒫` has `474` nodes: `82` variable nodes, `6` constant
   nodes with values `0, 1, 4, 2, 3, -1` in node order, `196` additions, `190` multiplications
   and no calls.

Item 2 is a kernel computation (`decide +kernel` on the `474`-node construction). Item 1 is not
evaluated: building the hash-consed node list of `ℋ` in the kernel costs about `4·10¹⁰` list
comparisons. Its call count and first two nodes are proved (`haltingCircuit_counts`,
`haltingCircuit_nodes_eq`); the remaining statistics are the named finite check
`HaltingNodeCheck`, a closed decidable proposition taken as a hypothesis by the statements that
use it. It was checked outside Lean by a transcription of the Lean builder applied to the
literal interpreter, which reproduces the saved universal circuit node for node.

(Blueprint: `compiler/natural/universal/halting-node-check.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Universal

open Natural

/-- The kinds of nodes. -/
inductive NodeKind
  | const
  | var
  | add
  | mul
  | call
  deriving DecidableEq, Repr

/-- The kind of a node. -/
def nodeKind : NatNode → NodeKind
  | .const _ => .const
  | .var _ => .var
  | .add _ _ => .add
  | .mul _ _ => .mul
  | .call _ _ _ _ => .call

/-- The number of nodes of kind `κ` in a node list. -/
def countKind (κ : NodeKind) (l : List NatNode) : ℕ := l.countP fun n => nodeKind n = κ

/-- The value of a constant node. -/
def constOf : NatNode → Option ℤ
  | .const c => some c
  | _ => none

/-- The values of the constant nodes, in node order. -/
def constList (l : List NatNode) : List ℤ := l.filterMap constOf

theorem length_eq_countKind (l : List NatNode) :
    l.length = countKind .var l + countKind .const l + countKind .add l + countKind .mul l +
      countKind .call l := by
  induction l with
  | nil => rfl
  | cons n l ih =>
    simp only [countKind, List.countP_cons, List.length_cons] at ih ⊢
    rw [ih]
    cases n <;> simp [nodeKind] <;> ring

theorem countKind_call (l : List NatNode) : countKind .call l = l.countP NatNode.isCall := by
  unfold countKind
  congr 1
  funext n
  cases n <;> rfl

theorem countKind_append (κ : NodeKind) (l l' : List NatNode) :
    countKind κ (l ++ l') = countKind κ l + countKind κ l' := List.countP_append ..

theorem constList_append (l l' : List NatNode) :
    constList (l ++ l') = constList l ++ constList l' := List.filterMap_append

/-! ### The power template (item 2), a kernel computation -/

set_option maxRecDepth 100000 in
/-- **Node statistics of the power template.** -/
theorem powerTemplate_nodeStats :
    (countKind .var powerTemplateCircuit.nodes, countKind .const powerTemplateCircuit.nodes,
      countKind .add powerTemplateCircuit.nodes, countKind .mul powerTemplateCircuit.nodes,
      countKind .call powerTemplateCircuit.nodes, constList powerTemplateCircuit.nodes) =
      (82, 6, 196, 190, 0, [0, 1, 4, 2, 3, -1]) := by
  decide +kernel

theorem powerTemplate_nodes_length : powerTemplateCircuit.nodes.length = 474 := by
  have h := powerTemplate_nodeStats
  simp only [Prod.mk.injEq] at h
  rw [length_eq_countKind, h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1]

/-! ### The halting circuit (item 1), a named finite check -/

/-- **FINITE CHECK** (input of milestone 1, to be replaced by a kernel certificate): the node
statistics of the universal halting circuit not proved symbolically. It is a closed decidable
proposition about the explicit construction `ℋ = 𝒞_{𝒰,2}`; it does not involve `c₃` or any
astronomically large constant. -/
def HaltingNodeCheck : Prop :=
  countKind .var haltingCircuit.nodes = 54049 ∧ countKind .const haltingCircuit.nodes = 6 ∧
  countKind .add haltingCircuit.nodes = 125307 ∧ countKind .mul haltingCircuit.nodes = 98361 ∧
  constList haltingCircuit.nodes = [0, 1, 2, 4, 1399, -1]

instance : Decidable HaltingNodeCheck := by unfold HaltingNodeCheck; infer_instance

theorem haltingCircuit_countKind_call : countKind .call haltingCircuit.nodes = 15845 := by
  rw [countKind_call]; exact haltingCircuit_counts.2.2.2.1

/-- **Node statistics of the universal halting circuit**, from the finite check. -/
theorem haltingCircuit_nodeStats (hN : HaltingNodeCheck) :
    haltingCircuit.nodes.length = 293568 ∧ countKind .var haltingCircuit.nodes = 54049 ∧
    countKind .const haltingCircuit.nodes = 6 ∧ countKind .add haltingCircuit.nodes = 125307 ∧
    countKind .mul haltingCircuit.nodes = 98361 ∧ countKind .call haltingCircuit.nodes = 15845 ∧
    constList haltingCircuit.nodes = [0, 1, 2, 4, 1399, -1] ∧
    haltingCircuit.nodes[0]? = some (.var 0) ∧ haltingCircuit.nodes[1]? = some (.var 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hN
  obtain ⟨rest, hr⟩ := haltingCircuit_nodes_eq
  refine ⟨?_, h1, h2, h3, h4, haltingCircuit_countKind_call, h5, by simp [hr], by simp [hr]⟩
  rw [length_eq_countKind, h1, h2, h3, h4, haltingCircuit_countKind_call]

end ZInQ.Compiler.Universal
