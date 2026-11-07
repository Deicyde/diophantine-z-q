import ZInQKernel.Size.Majorants.Basic

/-!
# Syntax heights

Blueprint: `size/majorants/syntax-height.md`.

Heights of the node-list syntax of `ZInQKernel.Syntax.Language.Nodes`:

* a variable has height `0`, a constant and a fixed node height `1`;
* an addition or multiplication, a psi node and a guard node have height one more than their
  highest argument;
* a call has height `1 + H(τ') + max(0, max_i h(a_i))`, with `H(τ')` the height of the callee;
* the intrinsic height of a template is the height of its root node, computed over the
  heights of the earlier templates of the library.

A model-evaluation recipe has height `max(4, max_κ (H(κ) + 3)) + 2` over the callees `κ` that
occur in its calls; a composition recipe has height `max_i H(κ_i) + 2` (sum of squares) or
`max_i H(κ_i) + 1` (product).

References to missing nodes, templates or recipes have height `0`, matching their
denotation `0` (resp. the empty existential polynomial). The majorant `Maj` itself is in
`ZInQKernel.Size.Majorants.Basic`.
-/

namespace ZInQ.Size

open ZInQ.Syntax

variable {E : Type}

/-- The largest entry of a list of heights (`0` for the empty list). -/
def listMax (l : List ℕ) : ℕ := l.foldr max 0

theorem le_listMax {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ listMax l := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem listMax_le {l : List ℕ} {a : ℕ} (h : ∀ b ∈ l, b ≤ a) : listMax l ≤ a := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons b l ih =>
    exact max_le (h b List.mem_cons_self) (ih fun c hc => h c (List.mem_cons_of_mem _ hc))

/-- The height of a node, given the heights `lib` of the earlier templates and the heights `hs`
of the earlier nodes. -/
def nodeHeight (lib hs : List ℕ) : Node E → ℕ
  | .var _ => 0
  | .const _ => 1
  | .fixed _ => 1
  | .add j k => 1 + max (hs.getD j 0) (hs.getD k 0)
  | .mul j k => 1 + max (hs.getD j 0) (hs.getD k 0)
  | .psi _ a _ => 1 + listMax (List.ofFn fun i => hs.getD (a i) 0)
  | .guard _ a => 1 + listMax (List.ofFn fun i => hs.getD (a i) 0)
  | .call t args _ => 1 + lib.getD t 0 + listMax (args.map fun j => hs.getD j 0)

/-- The heights of all nodes of a node list, computed in one pass in stored order. -/
def nodeHeights (lib : List ℕ) (nodes : List (Node E)) : List ℕ :=
  nodes.foldl (fun hs n => hs ++ [nodeHeight lib hs n]) []

/-- The intrinsic height `H(τ)` of a template: the height of its root node. -/
def templateHeight (lib : List ℕ) (t : Template E) : ℕ :=
  (nodeHeights lib t.nodes).getD t.root 0

/-- The intrinsic heights of a library, computed in stored order. -/
def libraryHeights (ts : List (Template E)) : List ℕ :=
  ts.foldl (fun lib t => lib ++ [templateHeight lib t]) []

theorem nodeHeights_append (lib : List ℕ) (nodes : List (Node E)) (n : Node E) :
    nodeHeights lib (nodes ++ [n]) =
      nodeHeights lib nodes ++ [nodeHeight lib (nodeHeights lib nodes) n] := by
  simp [nodeHeights, List.foldl_append]

theorem length_nodeHeights (lib : List ℕ) (nodes : List (Node E)) :
    (nodeHeights lib nodes).length = nodes.length := by
  induction nodes using List.reverseRecOn with
  | nil => rfl
  | append_singleton nodes n ih => simp [nodeHeights_append, ih]

theorem libraryHeights_append (ts : List (Template E)) (t : Template E) :
    libraryHeights (ts ++ [t]) = libraryHeights ts ++ [templateHeight (libraryHeights ts) t] := by
  simp [libraryHeights, List.foldl_append]

theorem length_libraryHeights (ts : List (Template E)) :
    (libraryHeights ts).length = ts.length := by
  induction ts using List.reverseRecOn with
  | nil => rfl
  | append_singleton ts t ih => simp [libraryHeights_append, ih]

/-! ### Recipe heights -/

/-- The heights of the callees of the calls of a model-evaluation recipe, in the order of its
conjuncts: the natural template for each source row with a start, the scalar template of each
constant definition, and the template or recipe of each operation. -/
def modelCalleeHeights (tH rH : List ℕ) (r : ModelRecipe) : List ℕ :=
  r.sources.filterMap (fun row => row.2.map fun _ => tH.getD r.natural 0) ++
    r.constants.map (fun d => tH.getD d.1 0) ++
    r.operations.map (fun
      | .add .. => tH.getD r.addition 0
      | .mul .. => tH.getD r.multiplication 0
      | .power .. => match r.power with
        | some i => rH.getD i 0
        | none => 0)

/-- The height of the callee of a composition call. -/
def callTargetHeight (tH rH : List ℕ) : CallTarget → ℕ
  | .template i => tH.getD i 0
  | .recipe i => rH.getD i 0

/-- The height of a recipe, given the template heights `tH` and the heights `rH` of the
earlier recipes: `max(4, max_κ (H(κ) + 3)) + 2` for a model-evaluation recipe,
`max_i H(κ_i) + 2` for a sum of squares and `max_i H(κ_i) + 1` for a product. -/
def recipeHeight (tH rH : List ℕ) : Recipe → ℕ
  | .model r => max 4 (listMax ((modelCalleeHeights tH rH r).map (· + 3))) + 2
  | .composition r =>
    listMax (r.calls.map fun c => callTargetHeight tH rH c.target) +
      match r.connective with
      | .sumSq => 2
      | .prod => 1

/-- The heights of a list of recipes, computed in stored order. -/
def recipeHeights (tH : List ℕ) (rs : List Recipe) : List ℕ :=
  rs.foldl (fun rH ρ => rH ++ [recipeHeight tH rH ρ]) []

theorem recipeHeights_append (tH : List ℕ) (rs : List Recipe) (ρ : Recipe) :
    recipeHeights tH (rs ++ [ρ]) = recipeHeights tH rs ++ [recipeHeight tH (recipeHeights tH rs) ρ] := by
  simp [recipeHeights, List.foldl_append]

end ZInQ.Size
