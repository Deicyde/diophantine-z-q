import ZInQKernel.Syntax.Language.Nodes
import ZInQKernel.Syntax.Language.Lifting

/-!
# Relational form of a model-evaluation recipe

The polynomial of a model-evaluation recipe `ρ` is the sum of the squares of its constraint
polynomials, the compilation of the conjunction of its conjuncts. If the call blocks of `ρ` are
pairwise disjoint, lie above the parameters and avoid every point reference and every other
constraint, and every variable lies below the variable count (the witness-scope facts,
`ScopedIn`), then `Rel_ρ(a)` holds exactly when some assignment `x` with `x_i = a_i` for the
parameters satisfies

1. the generator equations `8x_{g₀} = 1641`, `4x_{g₁} = -15465`, `32x_{g₂} = 87483`;
2. `Rel_natural(ref(r)(x))` for every source row `(r, s)` with a natural start `s`;
3. `Rel_{S_h}(ref(-2)(x), ref(r)(x))` for every constant definition `(S_h, r, s)`;
4. the raw-addition, multiplication and power relations of the operations;
5. `ref(r)(x) = ref(r')(x)` for the root equality `(r, r')`

(`modelRecipe_rel_iff`). Under condition 1 the references `-1, -2, -3` are the codes of `O`,
`P₀` and `-P₀` (`Syntax.pointRef_eval_generator`). The callee relations are stated on lists of
codes (`CodeRel`).

The witness-scope facts of the translated recipes are part of the syntax chapter (witness scope
of constructed recipes); here they are the hypothesis `ScopedIn`.

(Blueprint: `compiler/translation/model-recipe-relation.md`.)
-/

namespace ZInQ.Translation

open Syntax MvPolynomial

/-! ### Calls on lists of codes -/

/-- The parameter values `(p₀, p₁, …)` of a call on the codes `ps`, coordinate by coordinate. -/
def codeArgs (ps : List (Fin 5 → ℚ)) (k : ℕ) : ℚ := (ps.flatMap List.ofFn).getD k 0

/-- `Rel_τ(p₀, p₁, …)` on a list of codes. -/
def CodeRel (τ : ExPoly) (ps : List (Fin 5 → ℚ)) : Prop := τ.Rel fun k => codeArgs ps k

/-- The rational code `ref(r)(x)` of a point reference. -/
noncomputable def refVal (g : Fin 3 → ℕ) (x : ℕ → ℚ) (r : ℤ) : Fin 5 → ℚ :=
  evCode x (pointRef g r)

theorem ev_getPoly (x : ℕ → ℚ) (l : List Poly) (k : ℕ) :
    ev x (getPoly l k) = (l.map (ev x)).getD k 0 := by
  simp only [getPoly, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[k]? <;> simp

theorem map_ev_pointRefList (g : Fin 3 → ℕ) (x : ℕ → ℚ) (r : ℤ) :
    (pointRefList g r).map (ev x) = List.ofFn (refVal g x r) := by
  simp [pointRefList, refVal, evCode]

theorem lift_callListFormula_one (τ : ExPoly) (g : Fin 3 → ℕ) (x : ℕ → ℚ) (a : ℤ) (s : ℕ) :
    (callListFormula τ (pointRefList g a) s).Lift x ↔ CodeRel τ [refVal g x a] := by
  simp only [callListFormula, Formula.lift_call, CodeRel, codeArgs, ev_getPoly,
    map_ev_pointRefList, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem lift_callListFormula_two (τ : ExPoly) (g : Fin 3 → ℕ) (x : ℕ → ℚ) (a b : ℤ) (s : ℕ) :
    (callListFormula τ (pointRefList g a ++ pointRefList g b) s).Lift x ↔
      CodeRel τ [refVal g x a, refVal g x b] := by
  simp only [callListFormula, Formula.lift_call, CodeRel, codeArgs, ev_getPoly, List.map_append,
    map_ev_pointRefList, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem lift_callListFormula_three (τ : ExPoly) (g : Fin 3 → ℕ) (x : ℕ → ℚ) (a b c : ℤ)
    (s : ℕ) :
    (callListFormula τ (pointRefList g a ++ pointRefList g b ++ pointRefList g c) s).Lift x ↔
      CodeRel τ [refVal g x a, refVal g x b, refVal g x c] := by
  simp only [callListFormula, Formula.lift_call, CodeRel, codeArgs, ev_getPoly, List.map_append,
    map_ev_pointRefList, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

theorem lift_callListFormula_four (τ : ExPoly) (g : Fin 3 → ℕ) (x : ℕ → ℚ) (a b c d : ℤ)
    (s : ℕ) :
    (callListFormula τ (pointRefList g a ++ pointRefList g b ++ pointRefList g c ++
        pointRefList g d) s).Lift x ↔
      CodeRel τ [refVal g x a, refVal g x b, refVal g x c, refVal g x d] := by
  simp only [callListFormula, Formula.lift_call, CodeRel, codeArgs, ev_getPoly, List.map_append,
    map_ev_pointRefList, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]

/-! ### The five conditions -/

/-- The power callee of a model-evaluation recipe (the empty polynomial if there is none). -/
noncomputable def powerCallee (recipes : List ExPoly) (r : ModelRecipe) : ExPoly :=
  match r.power with
  | some i => getEx recipes i
  | none => ExPoly.empty

/-- The relation of an operation at `x`. -/
def OpHolds (α μ π : ExPoly) (g : Fin 3 → ℕ) (x : ℕ → ℚ) : Operation → Prop
  | .add a b o _ => CodeRel α [refVal g x a, refVal g x b, refVal g x o]
  | .mul a b o _ => CodeRel μ [refVal g x a, refVal g x b, refVal g x o]
  | .power a b c o _ => CodeRel π [refVal g x a, refVal g x b, refVal g x c, refVal g x o]

/-- Conditions 1–4 of the relational form (all but the root equality). -/
structure ModelHoldsExceptRoot (templates recipes : List ExPoly) (r : ModelRecipe)
    (x : ℕ → ℚ) : Prop where
  /-- The generator equations. -/
  generator : x (r.generator 0) = 1641 / 8 ∧ x (r.generator 1) = -15465 / 4 ∧
    x (r.generator 2) = 87483 / 32
  /-- The natural calls of the source rows with a natural start. -/
  natural : ∀ row ∈ r.sources, ∀ s, row.2 = some s →
    CodeRel (getEx templates r.natural) [refVal r.generator x row.1]
  /-- The constant definitions. -/
  constants : ∀ d ∈ r.constants,
    CodeRel (getEx templates d.1) [refVal r.generator x (-2), refVal r.generator x d.2.1]
  /-- The operations. -/
  operations : ∀ op ∈ r.operations, OpHolds (getEx templates r.addition)
    (getEx templates r.multiplication) (powerCallee recipes r) r.generator x op

/-- Conditions 1–5 of the relational form. -/
structure ModelHolds (templates recipes : List ExPoly) (r : ModelRecipe) (x : ℕ → ℚ) : Prop
    extends ModelHoldsExceptRoot templates recipes r x where
  /-- The root equality. -/
  root : refVal r.generator x r.rootEq.1 = refVal r.generator x r.rootEq.2

/-- The conjuncts of a model-evaluation recipe hold (with every call replaced by the callee
relation) exactly when conditions 1–5 hold. -/
theorem lift_formula_iff (templates recipes : List ExPoly) (r : ModelRecipe) (x : ℕ → ℚ) :
    (r.formula templates recipes).Lift x ↔ ModelHolds templates recipes r x := by
  simp only [ModelRecipe.formula, Formula.lift_and, ModelRecipe.conjuncts, List.forall_mem_append,
    List.forall_mem_map, Formula.lift_atom, List.mem_filterMap, Option.map_eq_some_iff,
    forall_exists_index, and_imp]
  rw [generatorConstraints_eq_zero_iff]
  have hroot : (∀ φ ∈ List.ofFn (fun i : Fin 5 => pointRef r.generator r.rootEq.1 i -
      pointRef r.generator r.rootEq.2 i), ev x φ = 0) ↔
      refVal r.generator x r.rootEq.1 = refVal r.generator x r.rootEq.2 := by
    simp only [List.forall_mem_ofFn_iff, map_sub, sub_eq_zero]
    exact ⟨fun h => funext h, fun h i => congrFun h i⟩
  rw [hroot]
  constructor
  · rintro ⟨⟨⟨⟨hg, hn⟩, hc⟩, ho⟩, hr⟩
    refine ⟨⟨hg, fun row hrow s hs => ?_, fun d hd => ?_, fun op hop => ?_⟩, hr⟩
    · exact (lift_callListFormula_one _ _ _ _ s).1 (hn _ row hrow s hs rfl)
    · exact (lift_callListFormula_two _ _ _ _ _ _).1 (hc d hd)
    · have := ho op hop
      cases op with
      | add a b o s => exact (lift_callListFormula_three _ _ _ _ _ _ _).1 this
      | mul a b o s => exact (lift_callListFormula_three _ _ _ _ _ _ _).1 this
      | power a b c o s => exact (lift_callListFormula_four _ _ _ _ _ _ _ _).1 this
  · rintro ⟨⟨hg, hn, hc, ho⟩, hr⟩
    refine ⟨⟨⟨⟨hg, fun φ row hrow s hs hφ => ?_⟩, fun d hd => ?_⟩, fun op hop => ?_⟩, hr⟩
    · subst hφ
      exact (lift_callListFormula_one _ _ _ _ s).2 (hn row hrow s hs)
    · exact (lift_callListFormula_two _ _ _ _ _ _).2 (hc d hd)
    · have := ho op hop
      cases op with
      | add a b o s => exact (lift_callListFormula_three _ _ _ _ _ _ _).2 this
      | mul a b o s => exact (lift_callListFormula_three _ _ _ _ _ _ _).2 this
      | power a b c o s => exact (lift_callListFormula_four _ _ _ _ _ _ _ _).2 this

/-! ### Private blocks of a recipe -/

/-- The witness-scope facts of a formula compiled with `p` parameters and `v` variables: callees
well formed, call blocks pairwise disjoint, above the parameters and avoided by the free
polynomials, and every variable below `v`. -/
structure ScopedIn (φ : Formula) (p v : ℕ) : Prop where
  /-- Callees well formed, blocks disjoint, free polynomials avoid the blocks. -/
  scope : φ.Scoped
  /-- The blocks lie above the parameters. -/
  above : ∀ b ∈ φ.blocks, p ≤ b.1
  /-- Every variable is below the variable count. -/
  varsLT : VarsLT φ.compile v
  /-- The parameters are among the variables. -/
  le : p ≤ v

/-- **Relations through private blocks.** Under the witness-scope facts, the relation of the
compiled formula holds at `a` exactly when some assignment extending `a` satisfies `φ^*`. -/
theorem rel_iff_lift {φ : Formula} {p v : ℕ} (h : ScopedIn φ p v) (a : Fin p → ℚ) :
    (⟨p, v - p, φ.compile⟩ : ExPoly).Rel a ↔
      ∃ x : ℕ → ℚ, (∀ i (hi : i < p), x i = a ⟨i, hi⟩) ∧ φ.Lift x := by
  have hb := Formula.exists_blocks_iff φ h.scope.wf h.scope.disjoint h.scope.free
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨assign p (v - p) a y, fun i hi => assign_of_lt a y hi,
      (hb _).1 ⟨_, fun _ _ => rfl, hy⟩⟩
  · rintro ⟨x, hxa, hl⟩
    obtain ⟨x', hx', hz⟩ := (hb x).2 hl
    refine ⟨fun j => x' (p + j), ?_⟩
    show ev (assign p (v - p) a _) φ.compile = 0
    rw [← hz]
    refine ev_congr fun i hi => ?_
    have hiv := h.varsLT i hi
    unfold assign
    split_ifs with h1 h2
    · rw [hx' i fun ⟨bl, hbl, hin⟩ => ?_, hxa i h1]
      have := h.above bl hbl
      exact absurd (lt_of_lt_of_le h1 (this.trans hin.1)) (lt_irrefl _)
    · show x' (p + (i - p)) = x' i
      rw [Nat.add_sub_cancel' (by omega)]
    · omega

/-- **Relational form of a model-evaluation recipe.** Under the witness-scope facts,
`Rel_ρ(a)` holds exactly when some assignment `x` extending the parameters `a` satisfies the
generator equations, the natural calls, the constant definitions, the operations and the root
equality. -/
theorem modelRecipe_rel_iff (templates recipes : List ExPoly) (r : ModelRecipe)
    (hsc : ScopedIn (r.formula templates recipes) r.parameterCount r.variableCount)
    (a : Fin r.parameterCount → ℚ) :
    ((Recipe.model r).denote templates recipes).Rel a ↔
      ∃ x : ℕ → ℚ, (∀ i (hi : i < r.parameterCount), x i = a ⟨i, hi⟩) ∧
        ModelHolds templates recipes r x := by
  have e : Recipe.poly templates recipes (.model r) = (r.formula templates recipes).compile :=
    Recipe.poly_eq_compile templates recipes (.model r)
  show (⟨r.parameterCount, r.variableCount - r.parameterCount,
    Recipe.poly templates recipes (.model r)⟩ : ExPoly).Rel a ↔ _
  rw [e, rel_iff_lift hsc]
  simp only [lift_formula_iff]

/-- Under the generator equations the references `-1, -2, -3` are `ι(0)`-shaped codes of `O`,
`P₀` and `-P₀`. -/
theorem refVal_generator {templates recipes : List ExPoly} {r : ModelRecipe} {x : ℕ → ℚ}
    (h : ModelHoldsExceptRoot templates recipes r x) :
    refVal r.generator x (-1) = ![1, 0, 0, 0, 0] ∧ refVal r.generator x (-2) = codeP0 ∧
      refVal r.generator x (-3) = codeNegP0 :=
  pointRef_eval_generator r.generator x ((generatorConstraints_eq_zero_iff _ _).2 h.generator)

end ZInQ.Translation
