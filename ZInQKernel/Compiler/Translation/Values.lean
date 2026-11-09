import ZInQKernel.Compiler.Circuits.Builder

/-!
# Values and polynomial of a natural circuit

Let `𝒩` be a natural circuit and `𝒫` a natural circuit with `3` inputs and no call nodes
(the power template), with `V_𝒫` variables.

* The value `val^𝒫_y(j)` of node `j` of `𝒫` at `y : ℕ → ℤ` is computed in node order:
  constants, variables, sums and products. `T_𝒫(y)` is the value of the root
  (`templateValue`).
* The value `val_θ(j)` of node `j` of `𝒩` at `θ : ℕ → ℤ` is computed by the same rules, a call
  node `call a b c w` having the value
  `T_𝒫(val_θ(a), val_θ(b), val_θ(c), θ_w, θ_{w+1}, …)` (`nodeVal`); the value of the circuit is
  `𝒩(θ) = val_θ(root)` (`circuitValue`). A call contributes the value of the power template;
  it does not assert that this value vanishes.
* The polynomial `[[𝒩]]` is the polynomial `NatCircuit.poly` of the natural chapter with call
  template `callTemplate 𝒫 = (3, V_𝒫 - 3, [[𝒫]])`; evaluation commutes with it
  (`circuitValue_eq_eval_poly`).
* `θ` is admissible when it is natural at the explicit witness variables and at every variable
  of the block `[w, w + V_𝒫 - 3)` of every call node; the inputs are not constrained.

The call value reads `θ_{w+i-3}` for every `i ≥ 3`; for a well-formed power template only
`i < V_𝒫` matters.

(Blueprint: `compiler/translation/natural-circuit-values.md`.)
-/

namespace ZInQ.Translation

open Compiler.Natural Syntax MvPolynomial

/-- The value of a node from the values `vals` of the earlier nodes; a call node
`call a b c w` has the value `callVal (val a) (val b) (val c) w`. Missing references read `0`. -/
def nodeValue (callVal : ℤ → ℤ → ℤ → ℕ → ℤ) (θ : ℕ → ℤ) (vals : List ℤ) : NatNode → ℤ
  | .const c => c
  | .var i => θ i
  | .add j k => vals.getD j 0 + vals.getD k 0
  | .mul j k => vals.getD j 0 * vals.getD k 0
  | .call a b c w => callVal (vals.getD a 0) (vals.getD b 0) (vals.getD c 0) w

/-- The values of all nodes, computed in one pass in stored order. -/
def nodeValues (callVal : ℤ → ℤ → ℤ → ℕ → ℤ) (θ : ℕ → ℤ) (nodes : List NatNode) : List ℤ :=
  nodes.foldl (fun vals n => vals ++ [nodeValue callVal θ vals n]) []

/-- `T_𝒫(y)`: the value of the root of a circuit without call nodes (call nodes, which a power
template does not have, read `0`). -/
def templateValue (P : NatCircuit) (y : ℕ → ℤ) : ℤ :=
  (nodeValues (fun _ _ _ _ => 0) y P.nodes).getD P.root 0

/-- The assignment `(a, b, c, θ_w, θ_{w+1}, …)` of a call with block start `w`. -/
def callAssign (θ : ℕ → ℤ) (a b c : ℤ) (w : ℕ) (i : ℕ) : ℤ :=
  if i < 3 then [a, b, c].getD i 0 else θ (w + (i - 3))

/-- The value `T_𝒫(a, b, c, θ_w, θ_{w+1}, …)` of a call node. -/
def callValue (P : NatCircuit) (θ : ℕ → ℤ) (a b c : ℤ) (w : ℕ) : ℤ :=
  templateValue P (callAssign θ a b c w)

/-- The values `val_θ(j)` of the nodes of `𝒩`, calls calling `𝒫`. -/
def nodeVals (P N : NatCircuit) (θ : ℕ → ℤ) : List ℤ := nodeValues (callValue P θ) θ N.nodes

/-- The value `val_θ(j)` of node `j` of `𝒩`. -/
def nodeVal (P N : NatCircuit) (θ : ℕ → ℤ) (j : ℕ) : ℤ := (nodeVals P N θ).getD j 0

/-- The value `𝒩(θ) = val_θ(root)` of the circuit. -/
def circuitValue (P N : NatCircuit) (θ : ℕ → ℤ) : ℤ := nodeVal P N θ N.root

/-- The call template of the power template `𝒫`: `3` parameters, `V_𝒫 - 3` witnesses, the
polynomial `[[𝒫]]`. -/
noncomputable def callTemplate (P : NatCircuit) : ExPoly :=
  ⟨3, P.varCount - 3, P.poly ExPoly.empty⟩

/-- The polynomial `[[𝒩]]` of `𝒩`, call nodes denoting the call of `[[𝒫]]` on the argument
polynomials and the block variables. -/
noncomputable def circuitPoly (P N : NatCircuit) : Poly := N.poly (callTemplate P)

/-- `θ` is admissible for `𝒩`: natural at every explicit witness variable and at every
variable of the block `[w, w + V_𝒫 - 3)` of every call node. -/
def Admissible (P N : NatCircuit) (θ : ℕ → ℤ) : Prop :=
  (∀ v ∈ N.explicitVars, v.2 = VarKind.witness → 0 ≤ θ v.1) ∧
    ∀ w ∈ N.blocks, ∀ i < P.varCount - 3, 0 ≤ θ (w + i)

/-! ### Evaluation commutes with the polynomial -/

theorem nodeValues_append (cv : ℤ → ℤ → ℤ → ℕ → ℤ) (θ : ℕ → ℤ) (l : List NatNode)
    (n : NatNode) :
    nodeValues cv θ (l ++ [n]) = nodeValues cv θ l ++ [nodeValue cv θ (nodeValues cv θ l) n] := by
  simp [nodeValues, List.foldl_append]

theorem length_nodeValues (cv : ℤ → ℤ → ℤ → ℕ → ℤ) (θ : ℕ → ℤ) (l : List NatNode) :
    (nodeValues cv θ l).length = l.length := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l n ih => simp [nodeValues_append, ih]

theorem getD_map_eval (θ : ℕ → ℤ) (vals : List Poly) (j : ℕ) :
    (vals.map (eval θ)).getD j 0 = eval θ (getPoly vals j) := by
  simp only [getPoly, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases vals[j]? <;> simp

/-- Node values are the evaluations of the node polynomials, if the call values are the
evaluations of the calls of `T`. -/
theorem nodeValues_eq_map (T : ExPoly) (cv : ℤ → ℤ → ℤ → ℕ → ℤ) (θ : ℕ → ℤ)
    (hcv : ∀ (A B C : Poly) (w : ℕ),
      eval θ (T.call (callArgs A B C T.params) w) = cv (eval θ A) (eval θ B) (eval θ C) w)
    (l : List NatNode) : nodeValues cv θ l = (denoteNatNodes T l).map (eval θ) := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l n ih =>
    rw [nodeValues_append, denoteNatNodes_append, List.map_append, ih]
    congr 1
    cases n <;> simp only [nodeValue, NatNode.denote, getD_map_eval, hcv, map_add, map_mul, eval_C,
      eval_X, List.map_cons, List.map_nil]

theorem eval_empty_call (θ : ℕ → ℤ) (A B C : Poly) (w : ℕ) :
    eval θ (ExPoly.empty.call (callArgs A B C ExPoly.empty.params) w) = 0 := by
  simp [ExPoly.call, ExPoly.empty, callPoly]

/-- `T_𝒫(y) = [[𝒫]](y)`. -/
theorem templateValue_eq_eval (P : NatCircuit) (y : ℕ → ℤ) :
    templateValue P y = eval y (P.poly ExPoly.empty) := by
  rw [templateValue, NatCircuit.poly, nodeValues_eq_map ExPoly.empty _ y
    (fun A B C w => eval_empty_call y A B C w), getD_map_eval]

theorem eval_callTemplate_call (P : NatCircuit) (θ : ℕ → ℤ) (A B D : Poly) (w : ℕ) :
    eval θ ((callTemplate P).call (callArgs A B D (callTemplate P).params) w) =
      callValue P θ (eval θ A) (eval θ B) (eval θ D) w := by
  rw [callValue, templateValue_eq_eval, ExPoly.call, callPoly, eval, eval₂Hom_bind₁]
  change eval _ (P.poly ExPoly.empty) = eval _ (P.poly ExPoly.empty)
  congr 2
  funext i
  simp only [callTemplate, callSubst, callAssign]
  split_ifs with h
  · interval_cases i <;> simp [callArgs, getPoly]
  · simp [h]

/-- **Evaluation commutes with the polynomial**: `𝒩(θ) = [[𝒩]](θ)`. -/
theorem circuitValue_eq_eval_poly (P N : NatCircuit) (θ : ℕ → ℤ) :
    circuitValue P N θ = eval θ (circuitPoly P N) := by
  rw [circuitValue, nodeVal, nodeVals, circuitPoly, NatCircuit.poly,
    nodeValues_eq_map (callTemplate P) _ θ (eval_callTemplate_call P θ), getD_map_eval]

/-- `val_θ(j)` is the evaluation of the polynomial of node `j`. -/
theorem nodeVal_eq_eval (P N : NatCircuit) (θ : ℕ → ℤ) (j : ℕ) :
    nodeVal P N θ j = eval θ (getPoly (denoteNatNodes (callTemplate P) N.nodes) j) := by
  rw [nodeVal, nodeVals, nodeValues_eq_map (callTemplate P) _ θ (eval_callTemplate_call P θ),
    getD_map_eval]

end ZInQ.Translation
