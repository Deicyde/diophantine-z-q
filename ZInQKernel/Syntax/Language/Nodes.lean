import ZInQKernel.Syntax.Language.PointRef
import ZInQKernel.Syntax.Language.Formula

/-!
# Semantics of templates and recipes

A template is stored as a node list in which every node refers only to earlier nodes; a
recipe is a list of composition calls or a model-evaluation record. Both denote existential
polynomials (`ExPoly`).

The three constructors `fixed`, `psi` and `guard` refer to fixed integer expressions, the
normalized division-polynomial components `Ψ_{n,c}` and the guard polynomials `G_T`. Their
meaning is supplied by a `Constructors` record: the value map `val`, the component polynomials
`Ψ_{n,c} ∈ ℤ[x₀,x₁,y₀,y₁]` and the guard polynomials `G_T ∈ ℤ[X_1,…,X_15]`. The node syntax is
parametric in the type `E` of fixed integer expressions, and nothing here evaluates `val`;
the chapters defining fixed expressions, division polynomials and the guard product
instantiate `Constructors`.

Node references that point to a later node, to a missing node or to a missing template are
read as `0` (resp. the empty existential polynomial); well-formed specifications never use
them.
-/

namespace ZInQ.Syntax

open MvPolynomial

/-- The meaning of the constructor symbols. -/
structure Constructors (E : Type) where
  /-- The value `val(e)` of a fixed integer expression. -/
  val : E → ℤ
  /-- The component polynomial `Ψ_{n,c}` in the four variables `x₀, x₁, y₀, y₁`. -/
  psi : ℤ → Fin 2 → MvPolynomial (Fin 4) ℤ
  /-- The guard polynomial `G_T` in fifteen variables (point-major order). -/
  guard : ℤ → MvPolynomial (Fin 15) ℤ

/-- Scalar nodes. -/
inductive Node (E : Type)
  /-- The constant `c`. -/
  | const (c : ℤ)
  /-- The local variable `X_i`. -/
  | var (i : ℕ)
  /-- The sum of nodes `j` and `k`. -/
  | add (j k : ℕ)
  /-- The product of nodes `j` and `k`. -/
  | mul (j k : ℕ)
  /-- The call of template `t` on the parameter nodes `args` with witness start `w`. -/
  | call (t : ℕ) (args : List ℕ) (w : ℕ)
  /-- The constant `val(e)`. -/
  | fixed (e : E)
  /-- `Ψ_{val(e),c}` at the four argument nodes. -/
  | psi (e : E) (a : Fin 4 → ℕ) (c : Fin 2)
  /-- `G_{val(e)}` at the fifteen argument nodes. -/
  | guard (e : E) (a : Fin 15 → ℕ)

/-- A template `(p, v, n_0, …, n_{k-1}, root)`. -/
structure Template (E : Type) where
  /-- The parameter count `p`. -/
  parameterCount : ℕ
  /-- The variable count `v ≥ p`. -/
  variableCount : ℕ
  /-- The node list. -/
  nodes : List (Node E)
  /-- The root node. -/
  root : ℕ

/-- The empty existential polynomial, used for missing references. -/
noncomputable def ExPoly.empty : ExPoly := ⟨0, 0, 0⟩

/-- Look up an entry of a list of polynomials, `0` if missing. -/
noncomputable def getPoly (vals : List Poly) (j : ℕ) : Poly := vals.getD j 0

/-- Look up an entry of a library of existential polynomials. -/
noncomputable def getEx (lib : List ExPoly) (t : ℕ) : ExPoly := lib.getD t ExPoly.empty

/-- The call `τ[l_0, …, l_{p-1}; w]` with the parameter polynomials given as a list. -/
noncomputable def ExPoly.callList (τ : ExPoly) (l : List Poly) (w : ℕ) : Poly :=
  τ.call (fun i => getPoly l i) w

variable {E : Type}

/-- The polynomial of a node, given the library `lib` of earlier templates and the
polynomials `vals` of the earlier nodes. -/
noncomputable def Node.denote (I : Constructors E) (lib : List ExPoly) (vals : List Poly) :
    Node E → Poly
  | .const c => C c
  | .var i => X i
  | .add j k => getPoly vals j + getPoly vals k
  | .mul j k => getPoly vals j * getPoly vals k
  | .call t args w => (getEx lib t).callList (args.map (getPoly vals)) w
  | .fixed e => C (I.val e)
  | .psi e a c => bind₁ (fun i => getPoly vals (a i)) (I.psi (I.val e) c)
  | .guard e a => bind₁ (fun i => getPoly vals (a i)) (I.guard (I.val e))

/-- The polynomials of all nodes of a node list, computed in one pass in stored order. -/
noncomputable def denoteNodes (I : Constructors E) (lib : List ExPoly) (nodes : List (Node E)) :
    List Poly :=
  nodes.foldl (fun vals n => vals ++ [n.denote I lib vals]) []

/-- The existential polynomial `[[τ]]` of a template: parameter count `p`, witness count
`v - p`, polynomial the polynomial of the root node. -/
noncomputable def Template.denote (I : Constructors E) (lib : List ExPoly) (t : Template E) :
    ExPoly :=
  ⟨t.parameterCount, t.variableCount - t.parameterCount,
    getPoly (denoteNodes I lib t.nodes) t.root⟩

/-- The library is denoted in its stored order; a call refers to an earlier template. -/
noncomputable def denoteLibrary (I : Constructors E) (ts : List (Template E)) : List ExPoly :=
  ts.foldl (fun lib t => lib ++ [t.denote I lib]) []

theorem denoteNodes_append (I : Constructors E) (lib : List ExPoly) (nodes : List (Node E))
    (n : Node E) :
    denoteNodes I lib (nodes ++ [n]) =
      denoteNodes I lib nodes ++ [n.denote I lib (denoteNodes I lib nodes)] := by
  simp [denoteNodes, List.foldl_append]

theorem length_denoteNodes (I : Constructors E) (lib : List ExPoly) (nodes : List (Node E)) :
    (denoteNodes I lib nodes).length = nodes.length := by
  induction nodes using List.reverseRecOn with
  | nil => rfl
  | append_singleton nodes n ih => simp [denoteNodes_append, ih]

/-- One pass in stored order: entry `i` is computed from the entries before it. -/
theorem getD_foldl_snoc {α β : Type*} (f : List β → α → β) (l : List α) {i : ℕ}
    (h : i < l.length) (d : β) :
    (l.foldl (fun acc a => acc ++ [f acc a]) []).getD i d =
      f ((l.take i).foldl (fun acc a => acc ++ [f acc a]) []) l[i] := by
  induction l using List.reverseRecOn with
  | nil => simp at h
  | append_singleton l a ih =>
    have hlen : (l.foldl (fun acc a => acc ++ [f acc a]) []).length = l.length := by
      clear ih h
      induction l using List.reverseRecOn with
      | nil => rfl
      | append_singleton l b ih => simp [List.foldl_append, ih]
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rcases Nat.lt_or_ge i l.length with hi | hi
    · rw [List.getD_append _ _ _ _ (by rw [hlen]; exact hi), ih hi, List.take_append_of_le_length hi.le,
        List.getElem_append_left hi]
    · have hi' : i = l.length := by simp at h; omega
      subst hi'
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]), hlen, Nat.sub_self, List.getD_cons_zero,
        List.take_left' rfl, List.getElem_append_right (by rfl)]
      simp

/-- The polynomial of node `j` is computed from the polynomials of the earlier nodes. -/
theorem getPoly_denoteNodes (I : Constructors E) (lib : List ExPoly) (nodes : List (Node E))
    {j : ℕ} (h : j < nodes.length) :
    getPoly (denoteNodes I lib nodes) j = nodes[j].denote I lib (denoteNodes I lib (nodes.take j)) :=
  getD_foldl_snoc _ nodes h 0

/-- Template `i` of the library is denoted over the templates before it. -/
theorem getEx_denoteLibrary (I : Constructors E) (ts : List (Template E)) {i : ℕ}
    (h : i < ts.length) :
    getEx (denoteLibrary I ts) i = ts[i].denote I (denoteLibrary I (ts.take i)) :=
  getD_foldl_snoc _ ts h _

/-! ### Recipes -/

/-- The connective of a composition recipe. -/
inductive Connective
  /-- Sum of squares (conjunction). -/
  | sumSq
  /-- Product (disjunction). -/
  | prod

/-- The callee of a composition call. -/
inductive CallTarget
  /-- A template of the library. -/
  | template (i : ℕ)
  /-- An earlier recipe. -/
  | recipe (i : ℕ)

/-- A composition call `(κ, (j_0, …, j_{p-1}), w)`. -/
structure RecipeCall where
  /-- The callee `κ`. -/
  target : CallTarget
  /-- The caller variables `j_0, …, j_{p-1}` passed as parameters. -/
  args : List ℕ
  /-- The witness start `w`. -/
  start : ℕ

/-- A composition recipe. -/
structure CompositionRecipe where
  /-- Sum of squares or product. -/
  connective : Connective
  /-- The parameter count. -/
  parameterCount : ℕ
  /-- The variable count. -/
  variableCount : ℕ
  /-- The calls. -/
  calls : List RecipeCall
  /-- Ranges `(start, length)` of fresh variables; they add no constraint. -/
  fresh : List (ℕ × ℕ)

/-- An operation of a model-evaluation recipe. -/
inductive Operation
  /-- Kind `0`: raw addition `(a, b, o)` with witness start `s`. -/
  | add (a b o : ℤ) (s : ℕ)
  /-- Kind `1`: multiplication `(a, b, o)` with witness start `s`. -/
  | mul (a b o : ℤ) (s : ℕ)
  /-- Kind `2`: power `(a, b, c, o)` with witness start `s`. -/
  | power (a b c o : ℤ) (s : ℕ)

/-- A model-evaluation recipe. -/
structure ModelRecipe where
  /-- The parameter count. -/
  parameterCount : ℕ
  /-- The variable count. -/
  variableCount : ℕ
  /-- The generator variable indices `g₀, g₁, g₂`. -/
  generator : Fin 3 → ℕ
  /-- Source variable rows `(r, s)`: a point reference and a natural start or none. -/
  sources : List (ℤ × Option ℕ)
  /-- Constant definitions `(σ, r, s)`: a scalar template, a point reference, a start. -/
  constants : List (ℕ × ℤ × ℕ)
  /-- The operations. -/
  operations : List Operation
  /-- The root equality `(r, r')`. -/
  rootEq : ℤ × ℤ
  /-- The natural template `ν`. -/
  natural : ℕ
  /-- The raw addition template `α`. -/
  addition : ℕ
  /-- The multiplication template `μ`. -/
  multiplication : ℕ
  /-- The power recipe `π`, if any. -/
  power : Option ℕ

/-- A recipe. -/
inductive Recipe
  /-- A composition recipe. -/
  | composition (r : CompositionRecipe)
  /-- A model-evaluation recipe. -/
  | model (r : ModelRecipe)

/-- The polynomial of a connective applied to a list of constraints. -/
noncomputable def Connective.apply : Connective → List Poly → Poly
  | .sumSq, cs => (cs.map (· ^ 2)).sum
  | .prod, cs => cs.prod

/-- The callee of a composition call, given the template library and the earlier recipes. -/
noncomputable def CallTarget.resolve (templates recipes : List ExPoly) : CallTarget → ExPoly
  | .template i => getEx templates i
  | .recipe i => getEx recipes i

/-- The call atom `τ[l_0, …, l_{p-1}; w]` with the parameter polynomials given as a list. -/
noncomputable def callListFormula (τ : ExPoly) (l : List Poly) (w : ℕ) : Formula :=
  .call τ (fun i => getPoly l i) w

@[simp] theorem compile_callListFormula (τ : ExPoly) (l : List Poly) (w : ℕ) :
    (callListFormula τ l w).compile = τ.callList l w := by
  simp [callListFormula, ExPoly.callList]

/-- The call atom `κ[X_{j_0}, …, X_{j_{p-1}}; w]` of a composition call. -/
noncomputable def RecipeCall.formula (templates recipes : List ExPoly) (c : RecipeCall) :
    Formula :=
  callListFormula (c.target.resolve templates recipes) (c.args.map X) c.start

/-- The constraint `κ[X_{j_0}, …, X_{j_{p-1}}; w]` of a composition call. -/
noncomputable def RecipeCall.constraint (templates recipes : List ExPoly) (c : RecipeCall) :
    Poly :=
  (c.formula templates recipes).compile

theorem RecipeCall.constraint_eq (templates recipes : List ExPoly) (c : RecipeCall) :
    c.constraint templates recipes =
      (c.target.resolve templates recipes).callList (c.args.map X) c.start := by
  simp [RecipeCall.constraint, RecipeCall.formula]

/-- The constraints of a composition recipe. -/
noncomputable def CompositionRecipe.constraints (templates recipes : List ExPoly)
    (r : CompositionRecipe) : List Poly :=
  r.calls.map (RecipeCall.constraint templates recipes)

/-- The conjuncts of a model-evaluation recipe, in the specification's order: the three
generator constraints, the natural calls of the source rows with a start, the constant
definitions, the operations, and the five differences of the root equality. -/
noncomputable def ModelRecipe.conjuncts (templates recipes : List ExPoly) (r : ModelRecipe) :
    List Formula :=
  let ref := pointRefList r.generator
  let ν := getEx templates r.natural
  let α := getEx templates r.addition
  let μ := getEx templates r.multiplication
  let π := match r.power with
    | some i => getEx recipes i
    | none => ExPoly.empty
  (generatorConstraints r.generator).map .atom ++
    r.sources.filterMap (fun row => row.2.map fun s => callListFormula ν (ref row.1) s) ++
    r.constants.map (fun d =>
      callListFormula (getEx templates d.1) (ref (-2) ++ ref d.2.1) d.2.2) ++
    r.operations.map (fun
      | .add a b o s => callListFormula α (ref a ++ ref b ++ ref o) s
      | .mul a b o s => callListFormula μ (ref a ++ ref b ++ ref o) s
      | .power a b c o s => callListFormula π (ref a ++ ref b ++ ref c ++ ref o) s) ++
    (List.ofFn fun i : Fin 5 =>
      pointRef r.generator r.rootEq.1 i - pointRef r.generator r.rootEq.2 i).map .atom

/-- The constraints of a model-evaluation recipe: the compiled conjuncts (the generator
polynomials, the call polynomials and the root differences). -/
noncomputable def ModelRecipe.constraints (templates recipes : List ExPoly) (r : ModelRecipe) :
    List Poly :=
  (r.conjuncts templates recipes).map Formula.compile

/-- The parameter count of a recipe. -/
def Recipe.parameterCount : Recipe → ℕ
  | .composition r => r.parameterCount
  | .model r => r.parameterCount

/-- The variable count of a recipe. -/
def Recipe.variableCount : Recipe → ℕ
  | .composition r => r.variableCount
  | .model r => r.variableCount

/-- The polynomial of a recipe: the connective applied to the constraints (a sum of squares
for model-evaluation recipes). -/
noncomputable def Recipe.poly (templates recipes : List ExPoly) : Recipe → Poly
  | .composition r => r.connective.apply (r.constraints templates recipes)
  | .model r => Connective.sumSq.apply (r.constraints templates recipes)

/-- The existential polynomial of a recipe. -/
noncomputable def Recipe.denote (templates recipes : List ExPoly) (ρ : Recipe) : ExPoly :=
  ⟨ρ.parameterCount, ρ.variableCount - ρ.parameterCount, ρ.poly templates recipes⟩

/-- The recipes are denoted in their stored order; a recipe calls only earlier recipes. -/
noncomputable def denoteRecipes (templates : List ExPoly) (rs : List Recipe) : List ExPoly :=
  rs.foldl (fun recipes ρ => recipes ++ [ρ.denote templates recipes]) []

/-- Recipe `i` is denoted over the recipes before it. -/
theorem getEx_denoteRecipes (templates : List ExPoly) (rs : List Recipe) {i : ℕ}
    (h : i < rs.length) :
    getEx (denoteRecipes templates rs) i = rs[i].denote templates (denoteRecipes templates (rs.take i)) :=
  getD_foldl_snoc _ rs h _

/-! ### Recipes as formulas -/

/-- The formula of a composition recipe: the conjunction or disjunction of its call atoms. -/
noncomputable def CompositionRecipe.formula (templates recipes : List ExPoly)
    (r : CompositionRecipe) : Formula :=
  match r.connective with
  | .sumSq => .and (r.calls.map (RecipeCall.formula templates recipes))
  | .prod => .or (r.calls.map (RecipeCall.formula templates recipes))

/-- The polynomial of a composition recipe is the compilation of its formula. -/
theorem CompositionRecipe.apply_constraints_eq (templates recipes : List ExPoly)
    (r : CompositionRecipe) :
    r.connective.apply (r.constraints templates recipes) = (r.formula templates recipes).compile := by
  have h : RecipeCall.constraint templates recipes =
      fun c => (RecipeCall.formula templates recipes c).compile := rfl
  unfold CompositionRecipe.formula CompositionRecipe.constraints
  cases r.connective <;>
    simp [Connective.apply, Formula.compile_and, Formula.compile_or, List.map_map,
      Function.comp_def, h]

/-- The formula of a model-evaluation recipe: the conjunction of its conjuncts. -/
noncomputable def ModelRecipe.formula (templates recipes : List ExPoly) (r : ModelRecipe) :
    Formula :=
  .and (r.conjuncts templates recipes)

/-- The polynomial of a model-evaluation recipe is the compilation of its formula. -/
theorem ModelRecipe.apply_constraints_eq (templates recipes : List ExPoly) (r : ModelRecipe) :
    Connective.sumSq.apply (r.constraints templates recipes) =
      (r.formula templates recipes).compile := by
  simp [Connective.apply, ModelRecipe.constraints, ModelRecipe.formula, Formula.compile_and,
    List.map_map, Function.comp_def]

/-- The polynomial of a recipe is the compilation of its formula. -/
noncomputable def Recipe.formula (templates recipes : List ExPoly) : Recipe → Formula
  | .composition r => r.formula templates recipes
  | .model r => r.formula templates recipes

theorem Recipe.poly_eq_compile (templates recipes : List ExPoly) (ρ : Recipe) :
    ρ.poly templates recipes = (ρ.formula templates recipes).compile := by
  cases ρ with
  | composition r => exact r.apply_constraints_eq templates recipes
  | model r => exact r.apply_constraints_eq templates recipes

/-! ### Semantics of the connectives -/

theorem ev_connective_sumSq_eq_zero_iff (x : ℕ → ℚ) (cs : List Poly) :
    ev x (Connective.sumSq.apply cs) = 0 ↔ ∀ c ∈ cs, ev x c = 0 :=
  ev_sum_sq_eq_zero_iff x cs

theorem ev_connective_prod_eq_zero_iff (x : ℕ → ℚ) (cs : List Poly) :
    ev x (Connective.prod.apply cs) = 0 ↔ ∃ c ∈ cs, ev x c = 0 :=
  ev_prod_eq_zero_iff x cs

theorem totalDegree_connective_sumSq_le (cs : List Poly) (D : ℕ)
    (h : ∀ c ∈ cs, c.totalDegree ≤ D) : (Connective.sumSq.apply cs).totalDegree ≤ 2 * D :=
  totalDegree_sum_sq_le cs D h

theorem totalDegree_connective_prod_le (cs : List Poly) :
    (Connective.prod.apply cs).totalDegree ≤ (cs.map totalDegree).sum :=
  totalDegree_list_prod cs

theorem VarsLT.connective {cs : List Poly} {N : ℕ} (h : ∀ c ∈ cs, VarsLT c N) (k : Connective) :
    VarsLT (k.apply cs) N := by
  cases k
  · exact VarsLT.list_sum fun f hf => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hf
      exact (h c hc).pow 2
  · exact VarsLT.list_prod h

end ZInQ.Syntax
