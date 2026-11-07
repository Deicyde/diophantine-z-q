import ZInQKernel.Assembly.Values.Gadgets
import ZInQKernel.Syntax.Recipes.Accounting
import ZInQKernel.Compiler.Translation.RecipeRelation

/-!
# Relations of the outer recipes

Blueprint: `assembly/value-templates/outer-recipe-relations.md`.

The outer recipes `close`, `main`, `value_union` and `value` are composition recipes
(`ZInQKernel/Syntax/Recipes/Outer.lean`). Their call blocks lie above their parameters and
fresh ranges, are pairwise disjoint and occur in no parameter list, so the private-witness
lemma replaces every call by the callee relation and the fresh ranges become existential
quantifiers (`compositionRecipe_rel_iff`).

Relations are stated on lists of rational values, `ValRel τ [v₀, v₁, …]`, so that no parameter
count of a recipe has to be evaluated; `valRel_ofFn_iff` converts to `Rel` at a vector.
The witness counts of the callees enter as hypotheses (`w` for the callee recipe); the theorems
hold for every template library and list of earlier recipes with these counts, in particular for
the specification (`specLib`).
-/

namespace ZInQ.Assembly

open Syntax MvPolynomial Translation

/-- `Rel_τ(v₀, v₁, …)` at a list of rational values (missing entries read as `0`). -/
def ValRel (τ : ExPoly) (l : List ℚ) : Prop := τ.Rel fun k => l.getD k 0

/-- `ValRel` at the entries of a vector of the right length. -/
theorem valRel_ofFn_iff (τ : ExPoly) {p : ℕ} (hp : τ.params = p) (v : Fin p → ℚ) :
    ValRel τ (List.ofFn v) ↔ τ.Rel fun k => v (Fin.cast hp k) := by
  unfold ValRel
  have : (fun k : Fin τ.params => (List.ofFn v).getD k 0) = fun k => v (Fin.cast hp k) := by
    funext k
    rw [List.getD_eq_getElem _ _ (by simp [← hp])]
    simp
    rfl
  rw [this]

/-! ### Composition recipes through their private blocks -/

theorem blocks_recipeCall_formula (T R : List ExPoly) (c : RecipeCall) :
    (c.formula T R).blocks = [(c.start, (c.target.resolve T R).witnesses)] := by
  simp [RecipeCall.formula, callListFormula, Formula.blocks]

theorem callees_recipeCall_formula (T R : List ExPoly) (c : RecipeCall) :
    (c.formula T R).callees = [c.target.resolve T R] := by
  simp [RecipeCall.formula, callListFormula, Formula.callees]

theorem freePolys_recipeCall_formula (T R : List ExPoly) (c : RecipeCall) :
    (c.formula T R).freePolys = List.ofFn fun i : Fin (c.target.resolve T R).params =>
      getPoly (c.args.map X) i := by
  simp [RecipeCall.formula, callListFormula, Formula.freePolys]

theorem vars_getPoly_map_X {args : List ℕ} {k i : ℕ} (h : i ∈ (getPoly (args.map X) k).vars) :
    i ∈ args := by
  unfold getPoly at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_map] at h
  cases hk : args[k]? with
  | none => simp [hk] at h
  | some j =>
    simp only [hk, Option.map_some, Option.getD_some, vars_X, Finset.mem_singleton] at h
    subst h
    exact List.mem_of_getElem? hk

/-- The parts of the formula of a composition recipe. -/
theorem compositionRecipe_formula_parts (T R : List ExPoly) (r : CompositionRecipe) :
    (r.formula T R).blocks = r.calls.map (fun c => (c.start, (c.target.resolve T R).witnesses)) ∧
    (r.formula T R).callees = r.calls.map (fun c => c.target.resolve T R) ∧
    (∀ f ∈ (r.formula T R).freePolys, ∀ i ∈ f.vars, ∃ c ∈ r.calls, i ∈ c.args) := by
  unfold CompositionRecipe.formula
  have key : (List.flatMap (fun φ => φ.blocks) (r.calls.map (RecipeCall.formula T R)) =
        r.calls.map (fun c => (c.start, (c.target.resolve T R).witnesses))) ∧
      (List.flatMap (fun φ => φ.callees) (r.calls.map (RecipeCall.formula T R)) =
        r.calls.map (fun c => c.target.resolve T R)) ∧
      (∀ f ∈ List.flatMap (fun φ => φ.freePolys) (r.calls.map (RecipeCall.formula T R)),
        ∀ i ∈ f.vars, ∃ c ∈ r.calls, i ∈ c.args) := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [List.flatMap_map, blocks_recipeCall_formula]
      generalize r.calls = l
      induction l with
      | nil => rfl
      | cons c l ih => simp [ih]
    · simp only [List.flatMap_map, callees_recipeCall_formula]
      generalize r.calls = l
      induction l with
      | nil => rfl
      | cons c l ih => simp [ih]
    · intro f hf i hi
      simp only [List.flatMap_map, List.mem_flatMap, freePolys_recipeCall_formula,
        List.mem_ofFn] at hf
      obtain ⟨c, hc, k, rfl⟩ := hf
      exact ⟨c, hc, vars_getPoly_map_X hi⟩
  cases r.connective
  · simpa only [Formula.blocks_and, Formula.callees_and, Formula.freePolys_and] using key
  · simpa only [Formula.blocks_or, Formula.callees_or, Formula.freePolys_or] using key

/-- **Relations of composition recipes.** If the arguments of the calls lie below `B` and the
call blocks lie at or above `B`, are pairwise disjoint and inside the variable count, then the
relation of the recipe is the formula with every call replaced by its callee relation, at some
assignment extending the parameters. -/
theorem compositionRecipe_rel_iff {T R : List ExPoly} {r : CompositionRecipe}
    (hr : r.InRange T R) {B : ℕ} (hp : r.parameterCount ≤ B)
    (hargs : ∀ c ∈ r.calls, ∀ j ∈ c.args, j < B) (hstart : ∀ c ∈ r.calls, B ≤ c.start)
    (hdisj : (r.calls.map fun c => (c.start, (c.target.resolve T R).witnesses)).Pairwise
      BlockDisjoint)
    (a : Fin r.parameterCount → ℚ) :
    ((Recipe.composition r).denote T R).Rel a ↔
      ∃ y : ℕ → ℚ, (∀ i : Fin r.parameterCount, y i = a i) ∧ (r.formula T R).Lift y := by
  obtain ⟨hbl, hca, hfr⟩ := compositionRecipe_formula_parts T R r
  have hscoped : (r.formula T R).Scoped := by
    refine ⟨fun τ hτ => ?_, hbl ▸ hdisj, fun f hf i hi hb => ?_⟩
    · rw [hca] at hτ
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hτ
      exact (hr.calls c hc).1
    · obtain ⟨c, hc, hic⟩ := hfr f hf i hi
      have := hargs c hc i hic
      rw [hbl] at hb
      obtain ⟨b, hb, hib⟩ := hb
      obtain ⟨c', hc', rfl⟩ := List.mem_map.1 hb
      have := hstart c' hc'
      exact absurd hib.1 (by omega)
  exact ExPoly.rel_iff_exists_lift (CompositionRecipe.denote_wf hr)
    (φ := r.formula T R) (Recipe.poly_eq_compile T R (.composition r)) hscoped
    (fun b hb => by
      rw [hbl] at hb
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
      exact hp.trans (hstart c hc)) a

/-- The call atom of a composition call. -/
theorem lift_recipeCall (T R : List ExPoly) (c : RecipeCall) (y : ℕ → ℚ) :
    (c.formula T R).Lift y ↔ ValRel (c.target.resolve T R) (c.args.map y) := by
  simp only [RecipeCall.formula, callListFormula, Formula.lift_call, ValRel, ev_getPoly,
    List.map_map]
  have : (ev y ∘ X) = y := funext fun i => ev_X y i
  simp only [this]

/-! ### Values of points and parameters -/

theorem map_point (y : ℕ → ℚ) (a : ℕ) : (point a).map y = List.ofFn (pointAt y a) := by
  rfl

theorem forall_fin_getD_iff {p : ℕ} (y : ℕ → ℚ) (l : List ℚ) (hl : l.length = p) :
    (∀ i : Fin p, y i = l.getD i 0) ↔ List.ofFn (fun i : Fin p => y i) = l := by
  constructor
  · intro h
    refine List.ext_getElem (by simp [hl]) fun i h1 h2 => ?_
    rw [List.getElem_ofFn, h ⟨i, by simpa using h1⟩, List.getD_eq_getElem _ _ h2]
  · rintro rfl i
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp

theorem ofFn_append_eq_iff {a b : Fin 5 → ℚ} {l₁ l₂ : List ℚ} :
    List.ofFn a ++ l₁ = List.ofFn b ++ l₂ ↔ a = b ∧ l₁ = l₂ := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    exact ⟨List.ofFn_injective h1, h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem ofFn_eleven {p : ℕ} (hp : p = 11) (y : ℕ → ℚ) : List.ofFn (fun i : Fin p => y i) =
    List.ofFn (pointAt y 0) ++ (List.ofFn (pointAt y 5) ++ [y 10]) := by
  subst hp; rfl

theorem ofFn_six {p : ℕ} (hp : p = 6) (y : ℕ → ℚ) :
    List.ofFn (fun i : Fin p => y i) = List.ofFn (pointAt y 0) ++ [y 5] := by
  subst hp; rfl

theorem pointAt_writeVals_writePoints (y : ℕ → ℚ) {pts : List (ℕ × (Fin 5 → ℚ))}
    (hsep : (pts.map Prod.fst).Pairwise Separated) {r : ℕ} {P : Fin 5 → ℚ} (h : (r, P) ∈ pts)
    {l : List (ℕ × ℚ)} (hl : ∀ e ∈ l, e.1 < r ∨ r + 5 ≤ e.1) :
    pointAt (writeVals (writePoints y pts) l) r = P := by
  rw [← evCode_writeVals_writePoints y hsep h hl, evCode_varPoint]
  rfl

/-! ### The four outer recipes -/

section Outer

variable {T R : List ExPoly}

/-- **Relation of `close`.** `Rel_close(N, K, t)` holds exactly when there are
`A, L, J, E₀, …, E₄` with `Rel_{value.signed_encode}(Σᵢ, Eᵢ)` for `(Σᵢ) = (N, K, A, L, J)`,
`Rel_precision(E₀, …, E₄)` and `Rel_{value.close_coordinates}(A, L, J, t)`. -/
theorem close_rel_iff (w : ℕ) (h13 : (getEx T 13).WF) (h13w : (getEx T 13).witnesses = 140654)
    (h15 : (getEx T 15).WF) (h15w : (getEx T 15).witnesses = 53) (h1 : (getEx R 1).WF)
    (h1w : (getEx R 1).witnesses = w) (N K : Fin 5 → ℚ) (t : ℚ) :
    ValRel ((Recipe.composition (closeRecipe w)).denote T R)
        (List.ofFn N ++ (List.ofFn K ++ [t])) ↔
      ∃ A L J E₀ E₁ E₂ E₃ E₄ : Fin 5 → ℚ,
        ValRel (getEx T 13) (List.ofFn N ++ List.ofFn E₀) ∧
        ValRel (getEx T 13) (List.ofFn K ++ List.ofFn E₁) ∧
        ValRel (getEx T 13) (List.ofFn A ++ List.ofFn E₂) ∧
        ValRel (getEx T 13) (List.ofFn L ++ List.ofFn E₃) ∧
        ValRel (getEx T 13) (List.ofFn J ++ List.ofFn E₄) ∧
        ValRel (getEx R 1) (List.ofFn E₀ ++ List.ofFn E₁ ++ List.ofFn E₂ ++ List.ofFn E₃ ++
          List.ofFn E₄) ∧
        ValRel (getEx T 15) (List.ofFn A ++ List.ofFn L ++ List.ofFn J ++ [t]) := by
  show ((Recipe.composition (closeRecipe w)).denote T R).Rel _ ↔ _
  refine (compositionRecipe_rel_iff (closeRecipe_inRange T R w h13 h13w h15 h15w h1 h1w) (B := 51)
    (by rw [closeRecipe_parameterCount]; omega)
    (by
      rw [closeRecipe_calls]
      intro c hc j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp only [List.mem_append, mem_point, List.mem_singleton] at hj <;> omega)
    (by
      rw [closeRecipe_calls]
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only <;> omega)
    (closeRecipe_callBlocks_disjoint T R w h13w h15w h1w) _).trans ?_
  simp only [CompositionRecipe.formula, closeRecipe_connective, closeRecipe_calls, List.map_cons,
    List.map_nil, Formula.lift_and, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, lift_recipeCall, CallTarget.resolve, List.map_append, map_point]
  simp only [forall_fin_getD_iff _ _ (show (List.ofFn N ++ (List.ofFn K ++ [t])).length =
    (closeRecipe w).parameterCount by simp; rfl), ofFn_eleven (show (closeRecipe w).parameterCount = 11 from rfl), ofFn_append_eq_iff, List.cons.injEq, and_true, List.map_cons,
    List.map_nil]
  constructor
  · rintro ⟨y, ⟨rfl, rfl, rfl⟩, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨_, _, _, _, _, _, _, _, h1, h2, h3, h4, h5, h6, h7⟩
  · rintro ⟨A, L, J, E₀, E₁, E₂, E₃, E₄, h1, h2, h3, h4, h5, h6, h7⟩
    let pts : List (ℕ × (Fin 5 → ℚ)) := [(0, N), (5, K), (11, A), (16, L), (21, J), (26, E₀),
      (31, E₁), (36, E₂), (41, E₃), (46, E₄)]
    have hsep : (pts.map Prod.fst).Pairwise Separated := by
      rw [show pts.map Prod.fst = [0, 5, 11, 16, 21, 26, 31, 36, 41, 46] from rfl]; decide
    let y := writeVals (writePoints (fun _ => 0) pts) [(10, t)]
    have hp : ∀ r P, (r, P) ∈ pts → pointAt y r = P := fun r P h =>
      pointAt_writeVals_writePoints _ hsep h (by
        intro e he
        simp only [List.mem_singleton] at he
        subst he
        simp only [pts, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h | h | h | h | h | h | h | h <;> obtain ⟨rfl, -⟩ := Prod.mk.inj h <;>
          simp)
    have ht : y 10 = t := by simp [y]
    refine ⟨y, ⟨hp _ _ (by simp [pts]), hp _ _ (by simp [pts]), ht⟩, ?_⟩
    rw [hp 0 N (by simp [pts]), hp 5 K (by simp [pts]), hp 11 A (by simp [pts]),
      hp 16 L (by simp [pts]), hp 21 J (by simp [pts]), hp 26 E₀ (by simp [pts]),
      hp 31 E₁ (by simp [pts]), hp 36 E₂ (by simp [pts]), hp 41 E₃ (by simp [pts]),
      hp 46 E₄ (by simp [pts]), ht]
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- **Relation of `main`.** `Rel_main(N, t) ⟺ ∃ K, Rel_close(N, K, t) ∧ Rel_{value.test}(N, K, t)`,
with the same coordinates of `K` in both calls. -/
theorem main_rel_iff (w : ℕ) (h16 : (getEx T 16).WF) (h16w : (getEx T 16).witnesses = 35282)
    (h2 : (getEx R 2).WF) (h2w : (getEx R 2).witnesses = w) (N : Fin 5 → ℚ) (t : ℚ) :
    ValRel ((Recipe.composition (mainRecipe w)).denote T R) (List.ofFn N ++ [t]) ↔
      ∃ K : Fin 5 → ℚ, ValRel (getEx R 2) (List.ofFn N ++ List.ofFn K ++ [t]) ∧
        ValRel (getEx T 16) (List.ofFn N ++ List.ofFn K ++ [t]) := by
  show ((Recipe.composition (mainRecipe w)).denote T R).Rel _ ↔ _
  refine (compositionRecipe_rel_iff (mainRecipe_inRange T R w h16 h16w h2 h2w) (B := 11)
    (by rw [mainRecipe_parameterCount]; omega)
    (by
      rw [mainRecipe_calls]
      intro c hc j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;>
        simp only [List.mem_append, mem_point, List.mem_singleton] at hj <;> omega)
    (by
      rw [mainRecipe_calls]
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp only <;> omega)
    (mainRecipe_callBlocks_disjoint T R w h16w h2w) _).trans ?_
  simp only [CompositionRecipe.formula, mainRecipe_connective, mainRecipe_calls, List.map_cons,
    List.map_nil, Formula.lift_and, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, lift_recipeCall, CallTarget.resolve, List.map_append, map_point]
  simp only [forall_fin_getD_iff _ _ (show (List.ofFn N ++ [t]).length = (mainRecipe w).parameterCount by
    simp; rfl), ofFn_six (show (mainRecipe w).parameterCount = 6 from rfl),
    ofFn_append_eq_iff, List.cons.injEq, and_true, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨y, ⟨rfl, rfl⟩, h1, h2⟩
    exact ⟨_, h1, h2⟩
  · rintro ⟨K, h1, h2⟩
    let pts : List (ℕ × (Fin 5 → ℚ)) := [(0, N), (6, K)]
    have hsep : (pts.map Prod.fst).Pairwise Separated := by
      rw [show pts.map Prod.fst = [0, 6] from rfl]; decide
    let y := writeVals (writePoints (fun _ => 0) pts) [(5, t)]
    have hp : ∀ r P, (r, P) ∈ pts → pointAt y r = P := fun r P h =>
      pointAt_writeVals_writePoints _ hsep h (by
        intro e he
        simp only [List.mem_singleton] at he
        subst he
        simp only [pts, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h <;> obtain ⟨rfl, -⟩ := Prod.mk.inj h <;> simp)
    have ht : y 5 = t := by simp [y]
    refine ⟨y, ⟨hp _ _ (by simp [pts]), ht⟩, ?_⟩
    rw [hp 0 N (by simp [pts]), hp 6 K (by simp [pts]), ht]
    exact ⟨h1, h2⟩

/-- **Relation of `value_union`.**
`Rel_{value_union}(N, t) ⟺ Rel_{value.exceptions}(N, t) ∨ Rel_main(N, t)`. -/
theorem valueUnion_rel_iff (w : ℕ) (h17 : (getEx T 17).WF) (h17w : (getEx T 17).witnesses = 406)
    (h3 : (getEx R 3).WF) (h3w : (getEx R 3).witnesses = w) (N : Fin 5 → ℚ) (t : ℚ) :
    ValRel ((Recipe.composition (valueUnionRecipe w)).denote T R) (List.ofFn N ++ [t]) ↔
      ValRel (getEx T 17) (List.ofFn N ++ [t]) ∨ ValRel (getEx R 3) (List.ofFn N ++ [t]) := by
  show ((Recipe.composition (valueUnionRecipe w)).denote T R).Rel _ ↔ _
  refine (compositionRecipe_rel_iff (valueUnionRecipe_inRange T R w h17 h17w h3 h3w) (B := 6)
    (by rw [valueUnionRecipe_parameterCount])
    (by
      rw [valueUnionRecipe_calls]
      intro c hc j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;>
        simp only [List.mem_append, mem_point, List.mem_singleton] at hj <;> omega)
    (by
      rw [valueUnionRecipe_calls]
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp only <;> omega)
    (valueUnionRecipe_callBlocks_disjoint T R w h17w h3w) _).trans ?_
  simp only [CompositionRecipe.formula, valueUnionRecipe_connective, valueUnionRecipe_calls,
    List.map_cons, List.map_nil, Formula.lift_or, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left, lift_recipeCall, CallTarget.resolve, List.map_append,
    map_point]
  simp only [forall_fin_getD_iff _ _ (show (List.ofFn N ++ [t]).length = (valueUnionRecipe w).parameterCount by
    simp; rfl), ofFn_six (show (valueUnionRecipe w).parameterCount = 6 from rfl),
    ofFn_append_eq_iff, List.cons.injEq, and_true, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨y, ⟨rfl, rfl⟩, h⟩
    exact h
  · intro h
    let y := writeVals (writePoints (fun _ => 0) [(0, N)]) [(5, t)]
    have hN : pointAt y 0 = N :=
      pointAt_writeVals_writePoints _ (by simp) (by simp) (by simp)
    have ht : y 5 = t := by simp [y]
    exact ⟨y, ⟨hN, ht⟩, by rw [hN, ht]; exact h⟩

/-- **Relation of `value`.** `Rel_value(N, t) ⟺ Rel_member(N) ∧ Rel_{value_union}(N, t)`. -/
theorem value_rel_iff (w : ℕ) (h0 : (getEx T 0).WF) (h0w : (getEx T 0).witnesses = 7)
    (h4 : (getEx R 4).WF) (h4w : (getEx R 4).witnesses = w) (N : Fin 5 → ℚ) (t : ℚ) :
    ValRel ((Recipe.composition (valueRecipe w)).denote T R) (List.ofFn N ++ [t]) ↔
      ValRel (getEx T 0) (List.ofFn N) ∧ ValRel (getEx R 4) (List.ofFn N ++ [t]) := by
  show ((Recipe.composition (valueRecipe w)).denote T R).Rel _ ↔ _
  refine (compositionRecipe_rel_iff (valueRecipe_inRange T R w h0 h0w h4 h4w) (B := 6)
    (by rw [valueRecipe_parameterCount])
    (by
      rw [valueRecipe_calls]
      intro c hc j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;>
        simp only [List.mem_append, mem_point, List.mem_singleton] at hj <;> omega)
    (by
      rw [valueRecipe_calls]
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp only <;> omega)
    (valueRecipe_callBlocks_disjoint T R w h0w h4w) _).trans ?_
  simp only [CompositionRecipe.formula, valueRecipe_connective, valueRecipe_calls, List.map_cons,
    List.map_nil, Formula.lift_and, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, lift_recipeCall, CallTarget.resolve, List.map_append, map_point]
  simp only [forall_fin_getD_iff _ _ (show (List.ofFn N ++ [t]).length = (valueRecipe w).parameterCount by
    simp; rfl), ofFn_six (show (valueRecipe w).parameterCount = 6 from rfl),
    ofFn_append_eq_iff, List.cons.injEq, and_true, List.map_cons, List.map_nil]
  constructor
  · rintro ⟨y, ⟨rfl, rfl⟩, h⟩
    exact h
  · intro h
    let y := writeVals (writePoints (fun _ => 0) [(0, N)]) [(5, t)]
    have hN : pointAt y 0 = N :=
      pointAt_writeVals_writePoints _ (by simp) (by simp) (by simp)
    have ht : y 5 = t := by simp [y]
    exact ⟨y, ⟨hN, ht⟩, by rw [hN, ht]; exact h⟩

end Outer

/-! ### The specification -/

section Spec

open Compiler.Natural (NatCircuit)

variable {E : Type} (I : Constructors E) (cstar ell T c3 : ℤ) (Nc : NatCircuit)

theorem valRel_signedEncode (N C : Fin 5 → ℚ) :
    ValRel (signedEncodeTemplate I cstar ell T) (List.ofFn N ++ List.ofFn C) ↔
      (signedEncodeTemplate I cstar ell T).Rel (Fin.append N C) := by
  rw [← List.ofFn_fin_append]
  exact valRel_ofFn_iff _ rfl _

theorem valRel_close (A L J : Fin 5 → ℚ) (t : ℚ) :
    ValRel closeTemplate (List.ofFn A ++ List.ofFn L ++ List.ofFn J ++ [t]) ↔
      closeTemplate.Rel (Fin.append (Fin.append (Fin.append A L) J) ![t]) := by
  rw [show [t] = List.ofFn ![t] from rfl, ← List.ofFn_fin_append, ← List.ofFn_fin_append,
    ← List.ofFn_fin_append]
  exact valRel_ofFn_iff _ rfl _

theorem valRel_valueTest (N K : Fin 5 → ℚ) (t : ℚ) :
    ValRel (valueTestTemplate I cstar ell T) (List.ofFn N ++ List.ofFn K ++ [t]) ↔
      (valueTestTemplate I cstar ell T).Rel (Fin.append (Fin.append N K) ![t]) := by
  rw [show [t] = List.ofFn ![t] from rfl, ← List.ofFn_fin_append, ← List.ofFn_fin_append]
  exact valRel_ofFn_iff _ rfl _

theorem valRel_exceptions (N : Fin 5 → ℚ) (t : ℚ) :
    ValRel exceptionsTemplate (List.ofFn N ++ [t]) ↔ exceptionsTemplate.Rel (Fin.append N ![t]) := by
  rw [show [t] = List.ofFn ![t] from rfl, ← List.ofFn_fin_append]
  exact valRel_ofFn_iff _ rfl _

theorem valRel_member (N : Fin 5 → ℚ) : ValRel memberTemplate (List.ofFn N) ↔ memberTemplate.Rel N :=
  valRel_ofFn_iff _ rfl _

/-- `Rel_close` of the specification. -/
theorem spec_close_rel_iff (N K : Fin 5 → ℚ) (t : ℚ) :
    ValRel (getEx (specLib I cstar ell T c3 Nc) 2) (List.ofFn N ++ (List.ofFn K ++ [t])) ↔
      ∃ A L J E₀ E₁ E₂ E₃ E₄ : Fin 5 → ℚ,
        (signedEncodeTemplate I cstar ell T).Rel (Fin.append N E₀) ∧
        (signedEncodeTemplate I cstar ell T).Rel (Fin.append K E₁) ∧
        (signedEncodeTemplate I cstar ell T).Rel (Fin.append A E₂) ∧
        (signedEncodeTemplate I cstar ell T).Rel (Fin.append L E₃) ∧
        (signedEncodeTemplate I cstar ell T).Rel (Fin.append J E₄) ∧
        ValRel (getEx (specLib I cstar ell T c3 Nc) 1) (List.ofFn E₀ ++ List.ofFn E₁ ++
          List.ofFn E₂ ++ List.ofFn E₃ ++ List.ofFn E₄) ∧
        closeTemplate.Rel (Fin.append (Fin.append (Fin.append A L) J) ![t]) := by
  rw [getEx_specLib I cstar ell T c3 Nc (by decide)]
  have h1 := getEx_specLib_take I cstar ell T c3 Nc (i := 2) (j := 1) (by decide) (by decide)
  refine (close_rel_iff (T := templateLibrary I cstar ell T c3) _
    (templateLibrary_getEx_wf I cstar ell T c3 13) (by rw [templateLibrary_getEx_witnesses]; rfl)
    (templateLibrary_getEx_wf I cstar ell T c3 15) (by rw [templateLibrary_getEx_witnesses]; rfl)
    (by rw [h1]; exact specLib_wf_1 I cstar ell T c3 Nc)
    (by rw [h1, getEx_specLib_witnesses I cstar ell T c3 Nc (by decide)]; rfl) N K t).trans ?_
  rw [h1]
  simp only [show getEx (templateLibrary I cstar ell T c3) 13 = signedEncodeTemplate I cstar ell T
    from rfl, show getEx (templateLibrary I cstar ell T c3) 15 = closeTemplate from rfl,
    valRel_signedEncode, valRel_close]

/-- `Rel_main` of the specification: one shared shift `K`. -/
theorem spec_main_rel_iff (N : Fin 5 → ℚ) (t : ℚ) :
    ValRel (getEx (specLib I cstar ell T c3 Nc) 3) (List.ofFn N ++ [t]) ↔
      ∃ K : Fin 5 → ℚ,
        ValRel (getEx (specLib I cstar ell T c3 Nc) 2) (List.ofFn N ++ (List.ofFn K ++ [t])) ∧
        (valueTestTemplate I cstar ell T).Rel (Fin.append (Fin.append N K) ![t]) := by
  rw [getEx_specLib I cstar ell T c3 Nc (by decide)]
  have h2 := getEx_specLib_take I cstar ell T c3 Nc (i := 3) (j := 2) (by decide) (by decide)
  refine (main_rel_iff (T := templateLibrary I cstar ell T c3) _
    (templateLibrary_getEx_wf I cstar ell T c3 16) (by rw [templateLibrary_getEx_witnesses]; rfl)
    (by rw [h2]; exact specLib_wf_2 I cstar ell T c3 Nc)
    (by rw [h2, getEx_specLib_witnesses I cstar ell T c3 Nc (by decide)]; rfl) N t).trans ?_
  rw [h2]
  simp only [show getEx (templateLibrary I cstar ell T c3) 16 = valueTestTemplate I cstar ell T
    from rfl, valRel_valueTest]
  simp only [List.append_assoc]

/-- `Rel_{value_union}` of the specification. -/
theorem spec_valueUnion_rel_iff (N : Fin 5 → ℚ) (t : ℚ) :
    ValRel (getEx (specLib I cstar ell T c3 Nc) 4) (List.ofFn N ++ [t]) ↔
      exceptionsTemplate.Rel (Fin.append N ![t]) ∨
        ValRel (getEx (specLib I cstar ell T c3 Nc) 3) (List.ofFn N ++ [t]) := by
  rw [getEx_specLib I cstar ell T c3 Nc (by decide)]
  have h3 := getEx_specLib_take I cstar ell T c3 Nc (i := 4) (j := 3) (by decide) (by decide)
  refine (valueUnion_rel_iff (T := templateLibrary I cstar ell T c3) _
    (templateLibrary_getEx_wf I cstar ell T c3 17) (by rw [templateLibrary_getEx_witnesses]; rfl)
    (by rw [h3]; exact specLib_wf_3 I cstar ell T c3 Nc)
    (by rw [h3, getEx_specLib_witnesses I cstar ell T c3 Nc (by decide)]; rfl) N t).trans ?_
  rw [h3]
  simp only [show getEx (templateLibrary I cstar ell T c3) 17 = exceptionsTemplate from rfl,
    valRel_exceptions]

/-- `Rel_value` of the specification. -/
theorem spec_value_rel_iff (N : Fin 5 → ℚ) (t : ℚ) :
    ValRel (getEx (specLib I cstar ell T c3 Nc) 5) (List.ofFn N ++ [t]) ↔
      memberTemplate.Rel N ∧ ValRel (getEx (specLib I cstar ell T c3 Nc) 4) (List.ofFn N ++ [t]) := by
  rw [getEx_specLib I cstar ell T c3 Nc (by decide)]
  have h4 := getEx_specLib_take I cstar ell T c3 Nc (i := 5) (j := 4) (by decide) (by decide)
  refine (value_rel_iff (T := templateLibrary I cstar ell T c3) _
    (templateLibrary_getEx_wf I cstar ell T c3 0) (by rw [templateLibrary_getEx_witnesses]; rfl)
    (by rw [h4]; exact specLib_wf_4 I cstar ell T c3 Nc)
    (by rw [h4, getEx_specLib_witnesses I cstar ell T c3 Nc (by decide)]; rfl) N t).trans ?_
  rw [h4]
  simp only [show getEx (templateLibrary I cstar ell T c3) 0 = memberTemplate from rfl,
    valRel_member]

end Spec

end ZInQ.Assembly
