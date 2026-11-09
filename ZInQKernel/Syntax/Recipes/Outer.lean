import ZInQKernel.Syntax.Templates

/-!
# The outer composition recipes

Blueprint: `syntax/recipes/outer-recipes.md`.

Five composition recipes assemble the ordinary-value relation, transcribing the
`composition(...)` calls of `construction/ordinary-integer-polynomial.js`. Each is built with
one allocation counter starting at its parameter count (`CompM`): a fresh range takes the next
`n` variables and is recorded, a call takes the next `m` variables as its witness block, where
`m` is the callee's witness count.

Template indices (`templateLibrary`): `member = 0`, `value.signed_encode = 13`,
`value.close_coordinates = 15`, `value.test = 16`, `value.exceptions = 17`. Recipe indices (in
the recipe order `power_value, precision, close, main, value_union, value, integers`):
`precision = 1`, `close = 2`, `main = 3`, `value_union = 4`, `value = 5`.

The witness count of the callee recipe is a parameter of each recipe (`wPrec`, `wClose`,
`wMain`, `wUnion`, `wValue`), so that no count is ever evaluated; the recipe list instantiates
them with the witness counts of the preceding recipes. With the counts of the witness
accounting the call starts are those of the blueprint (`closeRecipe_calls`, …), and the call
blocks `[w, w + m)` of each recipe are pairwise disjoint (`closeRecipe_callBlocks_disjoint`, …,
`integersRecipe_callBlocks_disjoint`; blueprint `syntax/language/builder-well-formed.md`).
-/

namespace ZInQ.Syntax

/-- The state of a composition: the counter, the calls and the fresh ranges so far. -/
structure CompState where
  /-- The allocation counter. -/
  next : ℕ
  /-- The calls. -/
  calls : List RecipeCall
  /-- The fresh ranges `(start, length)`. -/
  fresh : List (ℕ × ℕ)

/-- Composition constructions. -/
def CompM (α : Type) : Type := CompState → α × CompState

namespace CompM

instance : Monad CompM where
  pure a s := (a, s)
  bind m f s := f (m s).1 (m s).2

/-- A fresh range of `n` variables; its start. -/
def fresh (n : ℕ) : CompM ℕ := fun s => (s.next, ⟨s.next + n, s.calls, s.fresh ++ [(s.next, n)]⟩)

/-- A call of `target` on the caller variables `args`, with a witness block of `m` variables. -/
def call (target : CallTarget) (args : List ℕ) (m : ℕ) : CompM Unit := fun s =>
  ((), ⟨s.next + m, s.calls ++ [⟨target, args, s.next⟩], s.fresh⟩)

/-- The composition recipe with connective `k` and `p` parameters built by `b`. -/
def run (k : Connective) (p : ℕ) (b : CompM Unit) : CompositionRecipe :=
  let s := (b ⟨p, [], []⟩).2
  ⟨k, p, s.next, s.calls, s.fresh⟩

end CompM

/-- The five variables `X_a, …, X_{a+4}` of a point. -/
def point (a : ℕ) : List ℕ := List.range' a 5

/-- **`close`** (sum of squares): parameters `N = X_0..4`, `K = X_5..9`, `t = X_10`; fresh points
`A, L, J, E_0, …, E_4`; calls `value.signed_encode[Σ_i, E_i]` for `(Σ_i) = (N, K, A, L, J)`,
`precision[E_0, …, E_4]` and `value.close_coordinates[A, L, J, t]`. -/
def closeRecipe (wPrec : ℕ) : CompositionRecipe := CompM.run .sumSq 11 do
  let A ← CompM.fresh 5
  let L ← CompM.fresh 5
  let J ← CompM.fresh 5
  let E0 ← CompM.fresh 5
  let E1 ← CompM.fresh 5
  let E2 ← CompM.fresh 5
  let E3 ← CompM.fresh 5
  let E4 ← CompM.fresh 5
  CompM.call (.template 13) (point 0 ++ point E0) 140654
  CompM.call (.template 13) (point 5 ++ point E1) 140654
  CompM.call (.template 13) (point A ++ point E2) 140654
  CompM.call (.template 13) (point L ++ point E3) 140654
  CompM.call (.template 13) (point J ++ point E4) 140654
  CompM.call (.recipe 1) (point E0 ++ point E1 ++ point E2 ++ point E3 ++ point E4) wPrec
  CompM.call (.template 15) (point A ++ point L ++ point J ++ [10]) 53

/-- **`main`** (sum of squares): parameters `N = X_0..4`, `t = X_5`; fresh point `K`; calls
`close[N, K, t]` and `value.test[N, K, t]` (the same coordinates of `K`). -/
def mainRecipe (wClose : ℕ) : CompositionRecipe := CompM.run .sumSq 6 do
  let K ← CompM.fresh 5
  CompM.call (.recipe 2) (point 0 ++ point K ++ [5]) wClose
  CompM.call (.template 16) (point 0 ++ point K ++ [5]) 35282

/-- **`value_union`** (product): parameters `N = X_0..4`, `t = X_5`; calls
`value.exceptions[N, t]` and `main[N, t]`. -/
def valueUnionRecipe (wMain : ℕ) : CompositionRecipe := CompM.run .prod 6 do
  CompM.call (.template 17) (point 0 ++ [5]) 406
  CompM.call (.recipe 3) (point 0 ++ [5]) wMain

/-- **`value`** (sum of squares): parameters `N = X_0..4`, `t = X_5`; calls `member[N]` and
`value_union[N, t]`. -/
def valueRecipe (wUnion : ℕ) : CompositionRecipe := CompM.run .sumSq 6 do
  CompM.call (.template 0) (point 0) 7
  CompM.call (.recipe 4) (point 0 ++ [5]) wUnion

/-- **`integers`** (sum of squares): parameter `t = X_0`; fresh point `N = X_1..5`; call
`value[N, t]`. -/
def integersRecipe (wValue : ℕ) : CompositionRecipe := CompM.run .sumSq 1 do
  let N ← CompM.fresh 5
  CompM.call (.recipe 5) (point N ++ [0]) wValue

/-! ### Counts and calls -/

theorem closeRecipe_parameterCount (w : ℕ) : (closeRecipe w).parameterCount = 11 := rfl

theorem closeRecipe_variableCount (w : ℕ) :
    (closeRecipe w).variableCount = 703321 + w + 53 := rfl

theorem closeRecipe_connective (w : ℕ) : (closeRecipe w).connective = .sumSq := rfl

theorem closeRecipe_calls (w : ℕ) : (closeRecipe w).calls =
    [⟨.template 13, point 0 ++ point 26, 51⟩,
      ⟨.template 13, point 5 ++ point 31, 51 + 140654⟩,
      ⟨.template 13, point 11 ++ point 36, 51 + 2 * 140654⟩,
      ⟨.template 13, point 16 ++ point 41, 51 + 3 * 140654⟩,
      ⟨.template 13, point 21 ++ point 46, 51 + 4 * 140654⟩,
      ⟨.recipe 1, point 26 ++ point 31 ++ point 36 ++ point 41 ++ point 46, 703321⟩,
      ⟨.template 15, point 11 ++ point 16 ++ point 21 ++ [10], 703321 + w⟩] := rfl

theorem closeRecipe_fresh (w : ℕ) : (closeRecipe w).fresh =
    [(11, 5), (16, 5), (21, 5), (26, 5), (31, 5), (36, 5), (41, 5), (46, 5)] := rfl

theorem mainRecipe_parameterCount (w : ℕ) : (mainRecipe w).parameterCount = 6 := rfl

theorem mainRecipe_variableCount (w : ℕ) : (mainRecipe w).variableCount = 11 + w + 35282 := rfl

theorem mainRecipe_connective (w : ℕ) : (mainRecipe w).connective = .sumSq := rfl

theorem mainRecipe_calls (w : ℕ) : (mainRecipe w).calls =
    [⟨.recipe 2, point 0 ++ point 6 ++ [5], 11⟩,
      ⟨.template 16, point 0 ++ point 6 ++ [5], 11 + w⟩] := rfl

theorem mainRecipe_fresh (w : ℕ) : (mainRecipe w).fresh = [(6, 5)] := rfl

theorem valueUnionRecipe_parameterCount (w : ℕ) : (valueUnionRecipe w).parameterCount = 6 := rfl

theorem valueUnionRecipe_variableCount (w : ℕ) :
    (valueUnionRecipe w).variableCount = 412 + w := rfl

theorem valueUnionRecipe_connective (w : ℕ) : (valueUnionRecipe w).connective = .prod := rfl

theorem valueUnionRecipe_calls (w : ℕ) : (valueUnionRecipe w).calls =
    [⟨.template 17, point 0 ++ [5], 6⟩, ⟨.recipe 3, point 0 ++ [5], 412⟩] := rfl

theorem valueUnionRecipe_fresh (w : ℕ) : (valueUnionRecipe w).fresh = [] := rfl

theorem valueRecipe_parameterCount (w : ℕ) : (valueRecipe w).parameterCount = 6 := rfl

theorem valueRecipe_variableCount (w : ℕ) : (valueRecipe w).variableCount = 13 + w := rfl

theorem valueRecipe_connective (w : ℕ) : (valueRecipe w).connective = .sumSq := rfl

theorem valueRecipe_calls (w : ℕ) : (valueRecipe w).calls =
    [⟨.template 0, point 0, 6⟩, ⟨.recipe 4, point 0 ++ [5], 13⟩] := rfl

theorem valueRecipe_fresh (w : ℕ) : (valueRecipe w).fresh = [] := rfl

theorem integersRecipe_parameterCount (w : ℕ) : (integersRecipe w).parameterCount = 1 := rfl

theorem integersRecipe_variableCount (w : ℕ) : (integersRecipe w).variableCount = 6 + w := rfl

theorem integersRecipe_connective (w : ℕ) : (integersRecipe w).connective = .sumSq := rfl

theorem integersRecipe_calls (w : ℕ) : (integersRecipe w).calls =
    [⟨.recipe 5, point 1 ++ [0], 6⟩] := rfl

theorem integersRecipe_fresh (w : ℕ) : (integersRecipe w).fresh = [(1, 5)] := rfl

/-! ### Call blocks -/

/-- The call blocks `(w, m)` of a composition recipe, `m` the witness count of the callee. -/
noncomputable def CompositionRecipe.callBlocks (T R : List ExPoly) (r : CompositionRecipe) :
    List (ℕ × ℕ) :=
  r.calls.map fun c => (c.start, (c.target.resolve T R).witnesses)

section CallBlocks

variable (T R : List ExPoly)

/-- The call blocks of `close` (one per call: five of `value.signed_encode`, `precision`,
`value.close_coordinates`) are pairwise disjoint. -/
theorem closeRecipe_callBlocks_disjoint (w : ℕ) (h13w : (getEx T 13).witnesses = 140654)
    (h15w : (getEx T 15).witnesses = 53) (h1w : (getEx R 1).witnesses = w) :
    ((closeRecipe w).callBlocks T R).Pairwise BlockDisjoint := by
  unfold CompositionRecipe.callBlocks
  rw [closeRecipe_calls]
  refine pairwise_blockDisjoint_of_sep ?_
  simp only [List.map_cons, List.map_nil, CallTarget.resolve, h13w, h15w, h1w, blocksSep,
    List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, false_imp_iff, implies_true]
  omega

theorem mainRecipe_callBlocks_disjoint (w : ℕ) (h16w : (getEx T 16).witnesses = 35282)
    (h2w : (getEx R 2).witnesses = w) :
    ((mainRecipe w).callBlocks T R).Pairwise BlockDisjoint := by
  unfold CompositionRecipe.callBlocks
  rw [mainRecipe_calls]
  refine pairwise_blockDisjoint_of_sep ?_
  simp only [List.map_cons, List.map_nil, CallTarget.resolve, h16w, h2w, blocksSep,
    List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, List.Pairwise.nil, and_true, false_imp_iff, implies_true]
  omega

theorem valueUnionRecipe_callBlocks_disjoint (w : ℕ) (h17w : (getEx T 17).witnesses = 406)
    (h3w : (getEx R 3).witnesses = w) :
    ((valueUnionRecipe w).callBlocks T R).Pairwise BlockDisjoint := by
  unfold CompositionRecipe.callBlocks
  rw [valueUnionRecipe_calls]
  refine pairwise_blockDisjoint_of_sep ?_
  simp only [List.map_cons, List.map_nil, CallTarget.resolve, h17w, h3w, blocksSep,
    List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, List.Pairwise.nil, and_true, false_imp_iff, implies_true]
  omega

theorem valueRecipe_callBlocks_disjoint (w : ℕ) (h0w : (getEx T 0).witnesses = 7)
    (h4w : (getEx R 4).witnesses = w) :
    ((valueRecipe w).callBlocks T R).Pairwise BlockDisjoint := by
  unfold CompositionRecipe.callBlocks
  rw [valueRecipe_calls]
  refine pairwise_blockDisjoint_of_sep ?_
  simp only [List.map_cons, List.map_nil, CallTarget.resolve, h0w, h4w, blocksSep,
    List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, List.Pairwise.nil, and_true, false_imp_iff, implies_true]
  omega

theorem integersRecipe_callBlocks_disjoint (w : ℕ) :
    ((integersRecipe w).callBlocks T R).Pairwise BlockDisjoint := by
  unfold CompositionRecipe.callBlocks
  rw [integersRecipe_calls]
  exact List.pairwise_singleton _ _

end CallBlocks

end ZInQ.Syntax
