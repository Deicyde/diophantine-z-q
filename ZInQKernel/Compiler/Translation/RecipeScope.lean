import ZInQKernel.Compiler.Translation.RecipeRelation

/-!
# Blocks and free variables of a model-evaluation recipe

The call blocks of the formula of a model-evaluation recipe are the natural blocks of its source
rows, the blocks of its constant definitions and the blocks of its operations, in this order
(`blocks_formula`). Every variable of a parameter polynomial or of an atom is a generator
variable or a coordinate of a point reference used by the recipe (`vars_freePolys`).
-/

namespace ZInQ.Translation

open Syntax MvPolynomial

/-- The point references of an operation. -/
def opRefs : Operation → List ℤ
  | .add a b o _ => [a, b, o]
  | .mul a b o _ => [a, b, o]
  | .power a b c o _ => [a, b, c, o]

/-- The point references used by a model-evaluation recipe. -/
def usedRefs (r : ModelRecipe) : List ℤ :=
  r.sources.map Prod.fst ++ ((-2) :: r.constants.map fun d => d.2.1) ++
    r.operations.flatMap opRefs ++ [r.rootEq.1, r.rootEq.2]

/-- The block of an operation, for the callee witness counts `α, μ, π`. -/
def opBlock (α μ π : ExPoly) : Operation → ℕ × ℕ
  | .add _ _ _ s => (s, α.witnesses)
  | .mul _ _ _ s => (s, μ.witnesses)
  | .power _ _ _ _ s => (s, π.witnesses)

theorem flatMap_singleton_eq_map {α β : Type*} (f : α → β) (l : List α) :
    (l.flatMap fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem blocks_callListFormula (τ : ExPoly) (l : List Poly) (s : ℕ) :
    (callListFormula τ l s).blocks = [(s, τ.witnesses)] := by
  simp [callListFormula, Formula.blocks]

theorem flatMap_blocks_filterMap (ν : ExPoly) (g : Fin 3 → ℕ) (l : List (ℤ × Option ℕ)) :
    (l.filterMap fun row => row.2.map fun s => callListFormula ν (pointRefList g row.1) s).flatMap
      Formula.blocks = l.filterMap fun row => row.2.map fun s => (s, ν.witnesses) := by
  induction l with
  | nil => rfl
  | cons row l ih =>
    obtain ⟨r, _ | s⟩ := row
    · simpa using ih
    · simp [ih, blocks_callListFormula]

/-- **The call blocks of a model-evaluation recipe.** -/
theorem blocks_formula (templates recipes : List ExPoly) (r : ModelRecipe) :
    (r.formula templates recipes).blocks =
      r.sources.filterMap (fun row => row.2.map fun s => (s, (getEx templates r.natural).witnesses)) ++
      r.constants.map (fun d => (d.2.2, (getEx templates d.1).witnesses)) ++
      r.operations.map (opBlock (getEx templates r.addition) (getEx templates r.multiplication)
        (powerCallee recipes r)) := by
  simp only [ModelRecipe.formula, Formula.blocks_and, ModelRecipe.conjuncts, List.flatMap_append,
    flatMap_blocks_filterMap]
  have h1 : ((generatorConstraints r.generator).map Formula.atom).flatMap Formula.blocks = [] := by
    simp [generatorConstraints, Formula.blocks]
  have h5 : ((List.ofFn fun i : Fin 5 => pointRef r.generator r.rootEq.1 i -
      pointRef r.generator r.rootEq.2 i).map Formula.atom).flatMap Formula.blocks = [] := by
    simp [Formula.blocks]
  rw [h1, h5, List.nil_append, List.append_nil]
  congr 1
  · congr 1
    rw [List.flatMap_map]
    simp only [blocks_callListFormula]
    exact flatMap_singleton_eq_map _ _
  · rw [List.flatMap_map]
    refine (List.flatMap_congr fun op _ => ?_).trans (flatMap_singleton_eq_map _ _)
    cases op with
    | add a b o s => simp [blocks_callListFormula, opBlock]
    | mul a b o s => simp [blocks_callListFormula, opBlock]
    | power a b c o s =>
      simp only [blocks_callListFormula, opBlock, powerCallee]
      cases r.power <;> rfl

/-! ### Free variables -/

theorem vars_145 : ((145 : Poly)).vars = ∅ := by
  rw [show (145 : Poly) = C 145 from (map_ofNat C 145).symm, vars_C]

theorem vars_neg_145 : ((-145 : Poly)).vars = ∅ := by
  rw [vars_neg, vars_145]

theorem vars_pointRef {g : Fin 3 → ℕ} {ρ : ℤ} {j : Fin 5} {i : ℕ}
    (h : i ∈ (pointRef g ρ j).vars) : (∃ m : Fin 3, i = g m) ∨ ∃ q : ℕ, ρ = q ∧ i = q + j := by
  classical
  rcases ρ with q | (_ | _ | _ | n)
  · right
    refine ⟨q, rfl, ?_⟩
    rw [Int.ofNat_eq_natCast, pointRef_natCast, vars_X, Finset.mem_singleton] at h
    exact h
  · change i ∈ ((![1, 0, 0, 0, 0] : Fin 5 → Poly) j).vars at h
    fin_cases j <;> simp at h
  · change i ∈ ((![0, X (g 0), -145, X (g 1), X (g 2)] : Fin 5 → Poly) j).vars at h
    fin_cases j
    · simp at h
    · left; exact ⟨0, by simpa [vars_X] using h⟩
    · simp [vars_145] at h
    · left; exact ⟨1, by simpa [vars_X] using h⟩
    · left; exact ⟨2, by simpa [vars_X] using h⟩
  · change i ∈ ((![0, X (g 0), -145, -X (g 1), -X (g 2)] : Fin 5 → Poly) j).vars at h
    fin_cases j
    · simp at h
    · left; exact ⟨0, by simpa [vars_X] using h⟩
    · simp [vars_145] at h
    · left; exact ⟨1, by simpa [vars_X, vars_neg] using h⟩
    · left; exact ⟨2, by simpa [vars_X, vars_neg] using h⟩
  · change i ∈ (0 : Poly).vars at h
    simp at h

/-- A variable occurring in the coordinates of a point reference. -/
def InRefs (g : Fin 3 → ℕ) (refs : List ℤ) (i : ℕ) : Prop :=
  (∃ m : Fin 3, i = g m) ∨ ∃ ρ ∈ refs, ∃ q : ℕ, ρ = q ∧ q ≤ i ∧ i < q + 5

theorem InRefs.mono {g : Fin 3 → ℕ} {refs refs' : List ℤ} {i : ℕ} (h : InRefs g refs i)
    (hs : ∀ ρ ∈ refs, ρ ∈ refs') : InRefs g refs' i := by
  rcases h with h | ⟨ρ, hρ, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨ρ, hs ρ hρ, h⟩

theorem inRefs_of_pointRef {g : Fin 3 → ℕ} {refs : List ℤ} {ρ : ℤ} (hρ : ρ ∈ refs) {j : Fin 5}
    {i : ℕ} (h : i ∈ (pointRef g ρ j).vars) : InRefs g refs i := by
  rcases vars_pointRef h with h | ⟨q, rfl, rfl⟩
  · exact Or.inl h
  · exact Or.inr ⟨q, hρ, q, rfl, by omega, by omega⟩

theorem inRefs_of_getPoly {g : Fin 3 → ℕ} {refs : List ℤ} {rs : List ℤ}
    (hrs : ∀ ρ ∈ rs, ρ ∈ refs) {k : ℕ} {i : ℕ}
    (h : i ∈ (getPoly (rs.flatMap (pointRefList g)) k).vars) : InRefs g refs i := by
  classical
  unfold getPoly at h
  rw [List.getD_eq_getElem?_getD] at h
  cases hk : (rs.flatMap (pointRefList g))[k]? with
  | none => rw [hk] at h; simp at h
  | some f =>
    rw [hk] at h
    have hf := List.mem_of_getElem? hk
    simp only [List.mem_flatMap, pointRefList, List.mem_ofFn] at hf
    obtain ⟨ρ, hρ, j, rfl⟩ := hf
    exact inRefs_of_pointRef (hrs ρ hρ) h

theorem freePolys_callListFormula (τ : ExPoly) (l : List Poly) (s : ℕ) :
    (callListFormula τ l s).freePolys = List.ofFn fun i : Fin τ.params => getPoly l i := by
  simp [callListFormula, Formula.freePolys]

theorem inRefs_of_call {g : Fin 3 → ℕ} {refs : List ℤ} {rs : List ℤ}
    (hrs : ∀ ρ ∈ rs, ρ ∈ refs) (τ : ExPoly) (s : ℕ) {f : Poly}
    (hf : f ∈ (callListFormula τ (rs.flatMap (pointRefList g)) s).freePolys) {i : ℕ}
    (hi : i ∈ f.vars) : InRefs g refs i := by
  rw [freePolys_callListFormula, List.mem_ofFn] at hf
  obtain ⟨k, rfl⟩ := hf
  exact inRefs_of_getPoly hrs hi

/-- **Free variables of a model-evaluation recipe.** Every variable of a parameter polynomial
or an atom is a generator variable or a coordinate of a used point reference. -/
theorem vars_freePolys (templates recipes : List ExPoly) (r : ModelRecipe) {f : Poly}
    (hf : f ∈ (r.formula templates recipes).freePolys) {i : ℕ} (hi : i ∈ f.vars) :
    InRefs r.generator (usedRefs r) i := by
  classical
  simp only [ModelRecipe.formula, Formula.freePolys_and, ModelRecipe.conjuncts, List.flatMap_append,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap, Option.map_eq_some_iff] at hf
  rcases hf with ((((⟨φ, ⟨c, hc, rfl⟩, hf⟩ | ⟨φ, ⟨row, hrow, s, hs, rfl⟩, hf⟩) |
    ⟨φ, ⟨d, hd, rfl⟩, hf⟩) | ⟨φ, ⟨op, hop, rfl⟩, hf⟩) | ⟨φ, ⟨c, hc, rfl⟩, hf⟩)
  · simp only [Formula.freePolys, List.mem_singleton] at hf
    rw [hf] at hi
    left
    simp only [generatorConstraints, List.mem_cons, List.not_mem_nil, or_false] at hc
    have h8 : ∀ (a : ℕ) (m : Fin 3) (c : Poly), c.vars = ∅ →
        i ∈ ((a : Poly) * X (r.generator m) + c).vars → ∃ m' : Fin 3, i = r.generator m' := by
      intro a m c hc hi
      rcases Finset.mem_union.1 (vars_add_subset _ _ hi) with h | h
      · rcases Finset.mem_union.1 (vars_mul _ _ h) with h' | h'
        · rw [show (a : Poly) = C (a : ℤ) from (map_natCast C a).symm, vars_C] at h'; simp at h'
        · rw [vars_X, Finset.mem_singleton] at h'; exact ⟨m, h'⟩
      · rw [hc] at h; simp at h
    have hc' : ∀ n : ℕ, ((-(n : Poly))).vars = ∅ := fun n => by
      rw [vars_neg, show (n : Poly) = C (n : ℤ) from (map_natCast C n).symm, vars_C]
    have hc'' : ∀ n : ℕ, ((n : Poly)).vars = ∅ := fun n => by
      rw [show (n : Poly) = C (n : ℤ) from (map_natCast C n).symm, vars_C]
    have hc2 : c = 8 * X (r.generator 0) - 1641 ∨ c = 4 * X (r.generator 1) + 15465 ∨
        c = 32 * X (r.generator 2) - 87483 := by simpa [generatorConstraints] using hc
    rcases hc2 with rfl | rfl | rfl
    · rw [sub_eq_add_neg] at hi
      exact h8 8 0 _ (by exact_mod_cast hc' 1641) (by exact_mod_cast hi)
    · exact h8 4 1 _ (by exact_mod_cast hc'' 15465) (by exact_mod_cast hi)
    · rw [sub_eq_add_neg] at hi
      exact h8 32 2 _ (by exact_mod_cast hc' 87483) (by exact_mod_cast hi)
  · have : pointRefList r.generator row.1 = [row.1].flatMap (pointRefList r.generator) := by simp
    rw [this] at hf
    exact inRefs_of_call (fun ρ hρ => by
      simp only [List.mem_singleton] at hρ; subst hρ
      simp only [usedRefs, List.mem_append, List.mem_map]
      exact Or.inl (Or.inl (Or.inl ⟨row, hrow, rfl⟩))) _ _ hf hi
  · have : pointRefList r.generator (-2) ++ pointRefList r.generator d.2.1 =
        [-2, d.2.1].flatMap (pointRefList r.generator) := by simp
    rw [this] at hf
    exact inRefs_of_call (fun ρ hρ => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
      simp only [usedRefs, List.mem_append, List.mem_cons, List.mem_map]
      rcases hρ with rfl | rfl
      · exact Or.inl (Or.inl (Or.inr (Or.inl rfl)))
      · exact Or.inl (Or.inl (Or.inr (Or.inr ⟨d, hd, rfl⟩)))) _ _ hf hi
  · have hsub : ∀ ρ ∈ opRefs op, ρ ∈ usedRefs r := fun ρ hρ => by
      simp only [usedRefs, List.mem_append, List.mem_flatMap]
      exact Or.inl (Or.inr ⟨op, hop, hρ⟩)
    cases op with
    | add a b o s =>
      have : pointRefList r.generator a ++ pointRefList r.generator b ++ pointRefList r.generator o =
          [a, b, o].flatMap (pointRefList r.generator) := by simp
      simp only at hf
      rw [this] at hf
      exact inRefs_of_call hsub _ _ hf hi
    | mul a b o s =>
      have : pointRefList r.generator a ++ pointRefList r.generator b ++ pointRefList r.generator o =
          [a, b, o].flatMap (pointRefList r.generator) := by simp
      simp only at hf
      rw [this] at hf
      exact inRefs_of_call hsub _ _ hf hi
    | power a b c o s =>
      have : pointRefList r.generator a ++ pointRefList r.generator b ++ pointRefList r.generator c ++
          pointRefList r.generator o = [a, b, c, o].flatMap (pointRefList r.generator) := by simp
      simp only at hf
      rw [this] at hf
      exact inRefs_of_call hsub _ _ hf hi
  · simp only [Formula.freePolys, List.mem_singleton] at hf
    subst hf
    rw [List.mem_ofFn] at hc
    obtain ⟨j, rfl⟩ := hc
    have h1 : r.rootEq.1 ∈ usedRefs r := by simp [usedRefs]
    have h2 : r.rootEq.2 ∈ usedRefs r := by simp [usedRefs]
    rcases Finset.mem_union.1 (vars_sub_subset (p := pointRef r.generator r.rootEq.1 j)
      (q := pointRef r.generator r.rootEq.2 j) hi) with h | h
    · exact inRefs_of_pointRef h1 h
    · exact inRefs_of_pointRef h2 h

/-! ### Callees -/

theorem callees_callListFormula (τ : ExPoly) (l : List Poly) (s : ℕ) :
    (callListFormula τ l s).callees = [τ] := by
  simp [callListFormula, Formula.callees]

/-- Every callee of a model-evaluation recipe is a template of the library or its power
callee. -/
theorem mem_callees_formula (templates recipes : List ExPoly) (r : ModelRecipe) {τ : ExPoly}
    (hτ : τ ∈ (r.formula templates recipes).callees) :
    (∃ i, τ = getEx templates i) ∨ τ = powerCallee recipes r := by
  simp only [ModelRecipe.formula, Formula.callees_and, ModelRecipe.conjuncts, List.flatMap_append,
    List.mem_append, List.mem_flatMap, List.mem_map, List.mem_filterMap,
    Option.map_eq_some_iff] at hτ
  rcases hτ with ((((⟨φ, ⟨c, hc, rfl⟩, hf⟩ | ⟨φ, ⟨row, hrow, s, hs, rfl⟩, hf⟩) |
    ⟨φ, ⟨d, hd, rfl⟩, hf⟩) | ⟨φ, ⟨op, hop, rfl⟩, hf⟩) | ⟨φ, ⟨c, hc, rfl⟩, hf⟩)
  · simp [Formula.callees] at hf
  · rw [callees_callListFormula, List.mem_singleton] at hf
    exact Or.inl ⟨_, hf⟩
  · rw [callees_callListFormula, List.mem_singleton] at hf
    exact Or.inl ⟨_, hf⟩
  · cases op with
    | add a b o s =>
      simp only [callees_callListFormula, List.mem_singleton] at hf
      exact Or.inl ⟨_, hf⟩
    | mul a b o s =>
      simp only [callees_callListFormula, List.mem_singleton] at hf
      exact Or.inl ⟨_, hf⟩
    | power a b c o s =>
      simp only [callees_callListFormula, List.mem_singleton] at hf
      right
      rw [hf, powerCallee]
      cases r.power <;> rfl
  · simp [Formula.callees] at hf

theorem ExPoly.empty_wf : ExPoly.empty.WF := VarsLT.zero _

theorem getEx_wf {lib : List ExPoly} (h : ∀ τ ∈ lib, τ.WF) (i : ℕ) : (getEx lib i).WF := by
  unfold getEx
  rw [List.getD_eq_getElem?_getD]
  cases hi : lib[i]? with
  | none => exact ExPoly.empty_wf
  | some τ => exact h τ (List.mem_of_getElem? hi)

theorem callees_wf_formula {templates recipes : List ExPoly} (ht : ∀ τ ∈ templates, τ.WF)
    (hr : ∀ τ ∈ recipes, τ.WF) (r : ModelRecipe) :
    ∀ τ ∈ (r.formula templates recipes).callees, τ.WF := by
  intro τ hτ
  rcases mem_callees_formula templates recipes r hτ with ⟨i, rfl⟩ | rfl
  · exact getEx_wf ht i
  · unfold powerCallee
    split
    · exact getEx_wf hr _
    · exact ExPoly.empty_wf

theorem callees_wf_formula' {templates recipes : List ExPoly} (ht : ∀ τ ∈ templates, τ.WF)
    (r : ModelRecipe) (hπ : (powerCallee recipes r).WF) :
    ∀ τ ∈ (r.formula templates recipes).callees, τ.WF := by
  intro τ hτ
  rcases mem_callees_formula templates recipes r hτ with ⟨i, rfl⟩ | rfl
  · exact getEx_wf ht i
  · exact hπ

end ZInQ.Translation
