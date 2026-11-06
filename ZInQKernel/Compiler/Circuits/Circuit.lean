import ZInQKernel.Compiler.Circuits.Compilation

/-!
# Natural semantics of a natural circuit

A natural circuit has `k` inputs, a list of explicit variables (index and kind, the inputs
first with indices `0, …, k-1`), a node list of constants, variables, sums, products and calls
`call a b c w` of the power template on three earlier nodes with block start `w`, a root node,
and a variable count `V`.

1. Its polynomial `[[𝒞]]` is the denotation of the root, the nodes being denoted in stored
   order and a call node denoting the power call `𝒫[[a], [b], [c]; w]` (literal substitution).
2. Its natural relation `Z_𝒞(c)` says that some natural values `z ∈ ℕ^{V-k}` of the remaining
   variables make `[[𝒞]](c, z)` vanish (variables of index at least `V` are set to `0`).
3. It is well scoped if every block `[w, w + 79)` lies in `[k, V)`, the blocks are pairwise
   disjoint and disjoint from the explicit variables, the explicit variables and the blocks
   cover `[0, V)`, and every variable node refers to an explicit variable.

The template `𝒫` is a parameter `T : ExPoly` of the denotation; the power template of
`PowerTemplate.lean` is the intended instance. Node references to later or missing nodes are
read as `0`.

(Blueprint: `compiler/natural/formulas/natural-circuit-semantics.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Natural

open Syntax MvPolynomial

/-- A natural circuit. -/
structure NatCircuit where
  /-- The number `k` of inputs. -/
  inputCount : ℕ
  /-- The explicit variables (index and kind), the inputs first. -/
  explicitVars : List (ℕ × VarKind)
  /-- The node list. -/
  nodes : List NatNode
  /-- The root node. -/
  root : ℕ
  /-- The variable count `V`. -/
  varCount : ℕ

/-- The polynomial of a node, given the polynomials `vals` of the earlier nodes; call nodes
call `T`. -/
def NatNode.denote (T : ExPoly) (vals : List Poly) : NatNode → Poly
  | .const c => C c
  | .var i => X i
  | .add j k => getPoly vals j + getPoly vals k
  | .mul j k => getPoly vals j * getPoly vals k
  | .call a b c w => T.call (callArgs (getPoly vals a) (getPoly vals b) (getPoly vals c) T.params) w

/-- The polynomials of all nodes, computed in one pass in stored order. -/
def denoteNatNodes (T : ExPoly) (nodes : List NatNode) : List Poly :=
  nodes.foldl (fun vals n => vals ++ [n.denote T vals]) []

namespace NatCircuit

/-- The polynomial `[[𝒞]]`: the denotation of the root. -/
def poly (T : ExPoly) (C : NatCircuit) : Poly := getPoly (denoteNatNodes T C.nodes) C.root

/-- The natural point `(c₀, …, c_{k-1}, z₀, …, z_{m-1}, 0, 0, …)`. -/
def natPoint (k m : ℕ) (c : Fin k → ℕ) (z : Fin m → ℕ) (i : ℕ) : ℕ :=
  if h : i < k then c ⟨i, h⟩ else if h' : i - k < m then z ⟨i - k, h'⟩ else 0

/-- The natural relation `Z_𝒞(c)`: some natural values of the other `V - k` variables make the
polynomial vanish. -/
def NatRel (T : ExPoly) (C : NatCircuit) (c : Fin C.inputCount → ℕ) : Prop :=
  ∃ z : Fin (C.varCount - C.inputCount) → ℕ,
    MvPolynomial.eval (fun i => (natPoint C.inputCount (C.varCount - C.inputCount) c z i : ℤ))
      (C.poly T) = 0

/-- The block starts of the call nodes, in node order. -/
def blocks (C : NatCircuit) : List ℕ :=
  C.nodes.filterMap fun n => match n with
    | .call _ _ _ w => some w
    | _ => none

/-- `i` lies in the block starting at `w`. -/
def InBlock (w i : ℕ) : Prop := w ≤ i ∧ i < w + powerWitnesses

/-- Well-scopedness (item 3). -/
structure WellScoped (C : NatCircuit) : Prop where
  /-- Every block lies in `[k, V)`. -/
  block_range : ∀ w ∈ C.blocks, C.inputCount ≤ w ∧ w + powerWitnesses ≤ C.varCount
  /-- The blocks are pairwise disjoint. -/
  blocks_disjoint : C.blocks.Pairwise fun w w' => ∀ i, InBlock w i → ¬ InBlock w' i
  /-- The blocks avoid the explicit variables. -/
  blocks_explicit : ∀ w ∈ C.blocks, ∀ v ∈ C.explicitVars, ¬ InBlock w v.1
  /-- The explicit variables and the blocks cover `[0, V)`. -/
  cover : ∀ i < C.varCount, (∃ v ∈ C.explicitVars, v.1 = i) ∨ ∃ w ∈ C.blocks, InBlock w i
  /-- Every variable node refers to an explicit variable. -/
  var_explicit : ∀ i, NatNode.var i ∈ C.nodes → ∃ v ∈ C.explicitVars, v.1 = i

end NatCircuit

/-- The initial state of a construction with `k` inputs `X_0, …, X_{k-1}`: their variable nodes
come first. -/
def State.init (k : ℕ) : State :=
  ⟨k, (List.range k).map fun i => (i, .input), (List.range k).map .var, [], []⟩

/-- The input expressions `X_0, …, X_{k-1}` (node `i` is the variable node of `X_i`). -/
def inputs (k : ℕ) : List Ex := (List.range k).map fun i => ⟨i, X i⟩

/-- The natural circuit of a construction with `k` inputs: its explicit variables, its node list
(with the node encoding of the final formula appended) and its root, and the final counter. -/
def NM.toCircuit (k : ℕ) (m : NM NForm) : NatCircuit :=
  let r := m (State.init k)
  let e := r.1.encode ExPoly.empty r.2
  ⟨k, e.2.vars, e.2.nodes, e.1.node, e.2.next⟩

theorem NM.toCircuit_explicitVars (k : ℕ) (m : NM NForm) : (m.toCircuit k).explicitVars =
    ((m (State.init k)).1.encode ExPoly.empty (m (State.init k)).2).2.vars := rfl

theorem NM.toCircuit_nodes (k : ℕ) (m : NM NForm) : (m.toCircuit k).nodes =
    ((m (State.init k)).1.encode ExPoly.empty (m (State.init k)).2).2.nodes := rfl

theorem NM.toCircuit_varCount (k : ℕ) (m : NM NForm) : (m.toCircuit k).varCount =
    ((m (State.init k)).1.encode ExPoly.empty (m (State.init k)).2).2.next := rfl

theorem NM.toCircuit_root (k : ℕ) (m : NM NForm) : (m.toCircuit k).root =
    ((m (State.init k)).1.encode ExPoly.empty (m (State.init k)).2).1.node := rfl

theorem NM.toCircuit_inputCount (k : ℕ) (m : NM NForm) : (m.toCircuit k).inputCount = k := rfl

/-- The formula of a construction with `k` inputs, read with call template `τ`. -/
def NM.formula (τ : ExPoly) (k : ℕ) (m : NM NForm) : Formula :=
  (m (State.init k)).1.toFormula τ

end ZInQ.Compiler.Natural
