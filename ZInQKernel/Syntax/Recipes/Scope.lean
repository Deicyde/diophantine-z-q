import ZInQKernel.Syntax.Recipes.Translate
import ZInQKernel.Syntax.Recipes.Outer

/-!
# Variable ranges of recipes

Every variable of a recipe polynomial has index below the recipe's variable count, provided
its point references, call arguments and witness blocks lie below it and its callees are well
formed (`ModelRecipe.denote_wf`, `CompositionRecipe.denote_wf`). For the translation of any
natural circuit these conditions hold by construction (`translate_denote_wf`): every reference
and every block is allocated by the counter.

(Part of `syntax/recipes/witness-accounting.md`, the variable-range half of
`syntax/language/builder-well-formed.md` for recipes.)
-/

namespace ZInQ.Syntax

open MvPolynomial
open ZInQ.Compiler.Natural (NatCircuit NatNode VarKind)

/-- A point reference whose variables lie below `V`: negative, or `r + 5 ≤ V`. -/
def RefOK (V : ℕ) (r : ℤ) : Prop := r < 0 ∨ r + 5 ≤ V

theorem RefOK.mono {V V' : ℕ} {r : ℤ} (h : RefOK V r) (hV : V ≤ V') : RefOK V' r := by
  unfold RefOK at *; omega

theorem RefOK.neg {V : ℕ} {r : ℤ} (h : r < 0) : RefOK V r := Or.inl h

theorem varsLT_pointRef {g : Fin 3 → ℕ} {V : ℕ} (hg : ∀ i, g i < V) {r : ℤ} (hr : RefOK V r)
    (i : Fin 5) : VarsLT (pointRef g r i) V := by
  match r, hr with
  | .ofNat n, hr =>
    rw [pointRef]
    refine VarsLT.X ?_
    simp only [RefOK, Int.ofNat_eq_natCast] at hr
    have := i.isLt
    omega
  | .negSucc 0, _ =>
    rw [pointRef]
    fin_cases i
    · exact VarsLT.one V
    all_goals exact VarsLT.zero V
  | .negSucc 1, _ =>
    rw [pointRef]
    fin_cases i
    · exact VarsLT.zero V
    · exact VarsLT.X (hg 0)
    · exact (VarsLT.ofNat 145 V).neg
    · exact VarsLT.X (hg 1)
    · exact VarsLT.X (hg 2)
  | .negSucc 2, _ =>
    rw [pointRef]
    fin_cases i
    · exact VarsLT.zero V
    · exact VarsLT.X (hg 0)
    · exact (VarsLT.ofNat 145 V).neg
    · exact (VarsLT.X (hg 1)).neg
    · exact (VarsLT.X (hg 2)).neg
  | .negSucc (k + 3), _ =>
    rw [pointRef]
    exact VarsLT.zero V

theorem varsLT_pointRefList {g : Fin 3 → ℕ} {V : ℕ} (hg : ∀ i, g i < V) {r : ℤ}
    (hr : RefOK V r) : ∀ f ∈ pointRefList g r, VarsLT f V := by
  intro f hf
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
  exact varsLT_pointRef hg hr i

theorem varsLT_getPoly {l : List Poly} {V : ℕ} (h : ∀ f ∈ l, VarsLT f V) (k : ℕ) :
    VarsLT (getPoly l k) V := by
  unfold getPoly
  rw [List.getD_eq_getElem?_getD]
  cases hk : l[k]? with
  | none => exact VarsLT.zero V
  | some f => exact h f (List.mem_of_getElem? hk)

theorem varsLT_callListFormula {τ : ExPoly} (hτ : τ.WF) {l : List Poly} {w V : ℕ}
    (hl : ∀ f ∈ l, VarsLT f V) (hw : w + τ.witnesses ≤ V) :
    VarsLT (callListFormula τ l w).compile V := by
  rw [compile_callListFormula, ExPoly.callList]
  exact ExPoly.varsLT_call hτ (fun k => varsLT_getPoly hl k) hw

theorem ExPoly.empty_wf : ExPoly.empty.WF := VarsLT.zero _

/-- A recipe whose polynomial has its variables below its variable count (not below its
parameter count) is well formed. -/
theorem Recipe.denote_wf {templates recipes : List ExPoly} {ρ : Recipe}
    (hp : ρ.parameterCount ≤ ρ.variableCount)
    (h : VarsLT (ρ.poly templates recipes) ρ.variableCount) : (ρ.denote templates recipes).WF := by
  unfold ExPoly.WF ExPoly.varCount Recipe.denote
  simp only
  rw [Nat.add_sub_cancel' hp]
  exact h

/-! ### Model-evaluation recipes -/

/-- The bounds of an operation: references below `V` and the witness block inside `[0, V)` for a
callee with witness counts `mα`, `mμ`, `mπ`. -/
def OpOK (V mα mμ mπ : ℕ) : Operation → Prop
  | .add a b o s => RefOK V a ∧ RefOK V b ∧ RefOK V o ∧ s + mα ≤ V
  | .mul a b o s => RefOK V a ∧ RefOK V b ∧ RefOK V o ∧ s + mμ ≤ V
  | .power a b c o s => RefOK V a ∧ RefOK V b ∧ RefOK V c ∧ RefOK V o ∧ s + mπ ≤ V

theorem OpOK.mono {V V' mα mμ mπ : ℕ} {op : Operation} (h : OpOK V mα mμ mπ op) (hV : V ≤ V') :
    OpOK V' mα mμ mπ op := by
  cases op with
  | add a b o s => exact ⟨h.1.mono hV, h.2.1.mono hV, h.2.2.1.mono hV, by have := h.2.2.2; omega⟩
  | mul a b o s => exact ⟨h.1.mono hV, h.2.1.mono hV, h.2.2.1.mono hV, by have := h.2.2.2; omega⟩
  | power a b c o s =>
    exact ⟨h.1.mono hV, h.2.1.mono hV, h.2.2.1.mono hV, h.2.2.2.1.mono hV,
      by have := h.2.2.2.2; omega⟩

/-- The power callee of a model-evaluation recipe. -/
noncomputable def ModelRecipe.powerCallee (recipes : List ExPoly) (r : ModelRecipe) : ExPoly :=
  match r.power with
  | some i => getEx recipes i
  | none => ExPoly.empty

/-- The range conditions of a model-evaluation recipe. -/
structure ModelRecipe.InRange (templates recipes : List ExPoly) (r : ModelRecipe) : Prop where
  params_le : r.parameterCount ≤ r.variableCount
  generator : ∀ i, r.generator i < r.variableCount
  natural_wf : (getEx templates r.natural).WF
  addition_wf : (getEx templates r.addition).WF
  multiplication_wf : (getEx templates r.multiplication).WF
  power_wf : (r.powerCallee recipes).WF
  sources : ∀ row ∈ r.sources, RefOK r.variableCount row.1 ∧
    ∀ s ∈ row.2, s + (getEx templates r.natural).witnesses ≤ r.variableCount
  constants : ∀ d ∈ r.constants, (getEx templates d.1).WF ∧ RefOK r.variableCount d.2.1 ∧
    d.2.2 + (getEx templates d.1).witnesses ≤ r.variableCount
  operations : ∀ op ∈ r.operations, OpOK r.variableCount (getEx templates r.addition).witnesses
    (getEx templates r.multiplication).witnesses (r.powerCallee recipes).witnesses op
  root : RefOK r.variableCount r.rootEq.1 ∧ RefOK r.variableCount r.rootEq.2

theorem ModelRecipe.varsLT_poly {templates recipes : List ExPoly} {r : ModelRecipe}
    (h : r.InRange templates recipes) :
    VarsLT ((Recipe.model r).poly templates recipes) r.variableCount := by
  have href : ∀ {x : ℤ}, RefOK r.variableCount x → ∀ f ∈ pointRefList r.generator x,
      VarsLT f r.variableCount := fun hx => varsLT_pointRefList h.generator hx
  have hm2 : ∀ (x : ℤ), RefOK r.variableCount (-2) := fun _ => RefOK.neg (by norm_num)
  refine VarsLT.sum_sq fun f hf => ?_
  simp only [ModelRecipe.constraints, ModelRecipe.conjuncts, List.map_append, List.mem_append,
    List.mem_map] at hf
  rcases hf with ((((⟨φ, ⟨c, hc, rfl⟩, rfl⟩ | ⟨φ, hφ, rfl⟩) | ⟨φ, ⟨d, hd, rfl⟩, rfl⟩) |
    ⟨φ, ⟨op, hop, rfl⟩, rfl⟩) | ⟨φ, ⟨c, hc, rfl⟩, rfl⟩)
  · -- generator constraints
    simp only [Formula.compile_atom]
    simp only [generatorConstraints, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ((VarsLT.ofNat 8 _).mul (VarsLT.X (h.generator 0))).sub (VarsLT.ofNat _ _)
    · exact ((VarsLT.ofNat 4 _).mul (VarsLT.X (h.generator 1))).add (VarsLT.ofNat _ _)
    · exact ((VarsLT.ofNat 32 _).mul (VarsLT.X (h.generator 2))).sub (VarsLT.ofNat _ _)
  · -- natural calls
    obtain ⟨row, hrow, hφ⟩ := List.mem_filterMap.1 hφ
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 hφ
    obtain ⟨h1, h2⟩ := h.sources row hrow
    exact varsLT_callListFormula h.natural_wf (href h1) (h2 s hs)
  · -- constant definitions
    obtain ⟨hd1, hd2, hd3⟩ := h.constants d hd
    refine varsLT_callListFormula hd1 (fun f hf => ?_) hd3
    rcases List.mem_append.1 hf with hf | hf
    · exact href (RefOK.neg (by norm_num)) f hf
    · exact href hd2 f hf
  · -- operations
    have hop' := h.operations op hop
    cases op with
    | add a b o s =>
      obtain ⟨ha, hb, ho, hs⟩ := hop'
      refine varsLT_callListFormula h.addition_wf (fun f hf => ?_) hs
      simp only [List.mem_append] at hf
      rcases hf with (hf | hf) | hf
      exacts [href ha f hf, href hb f hf, href ho f hf]
    | mul a b o s =>
      obtain ⟨ha, hb, ho, hs⟩ := hop'
      refine varsLT_callListFormula h.multiplication_wf (fun f hf => ?_) hs
      simp only [List.mem_append] at hf
      rcases hf with (hf | hf) | hf
      exacts [href ha f hf, href hb f hf, href ho f hf]
    | power a b c o s =>
      obtain ⟨ha, hb, hc, ho, hs⟩ := hop'
      have hπ := h.power_wf
      unfold ModelRecipe.powerCallee at hπ hs
      refine varsLT_callListFormula hπ (fun f hf => ?_) hs
      simp only [List.mem_append] at hf
      rcases hf with ((hf | hf) | hf) | hf
      exacts [href ha f hf, href hb f hf, href hc f hf, href ho f hf]
  · -- root differences
    simp only [Formula.compile_atom]
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hc
    exact (varsLT_pointRef h.generator h.root.1 i).sub (varsLT_pointRef h.generator h.root.2 i)

theorem ModelRecipe.denote_wf {templates recipes : List ExPoly} {r : ModelRecipe}
    (h : r.InRange templates recipes) : ((Recipe.model r).denote templates recipes).WF :=
  Recipe.denote_wf h.params_le (ModelRecipe.varsLT_poly h)

/-! ### Composition recipes -/

/-- The range conditions of a composition recipe. -/
structure CompositionRecipe.InRange (templates recipes : List ExPoly) (r : CompositionRecipe) :
    Prop where
  params_le : r.parameterCount ≤ r.variableCount
  calls : ∀ c ∈ r.calls, (c.target.resolve templates recipes).WF ∧
    (∀ j ∈ c.args, j < r.variableCount) ∧
    c.start + (c.target.resolve templates recipes).witnesses ≤ r.variableCount

theorem CompositionRecipe.varsLT_poly {templates recipes : List ExPoly} {r : CompositionRecipe}
    (h : r.InRange templates recipes) :
    VarsLT ((Recipe.composition r).poly templates recipes) r.variableCount := by
  refine VarsLT.connective (fun f hf => ?_) r.connective
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hf
  obtain ⟨h1, h2, h3⟩ := h.calls c hc
  refine varsLT_callListFormula h1 (fun f hf => ?_) h3
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hf
  exact VarsLT.X (h2 j hj)

theorem CompositionRecipe.denote_wf {templates recipes : List ExPoly} {r : CompositionRecipe}
    (h : r.InRange templates recipes) : ((Recipe.composition r).denote templates recipes).WF :=
  Recipe.denote_wf h.params_le (CompositionRecipe.varsLT_poly h)

/-! ### The translation is in range -/

section Translate

variable (p mπ : ℕ)

/-- The invariant of a translation state: everything recorded lies below the counter. -/
structure TrInv (s : TrState) : Prop where
  base : p + 3 ≤ s.next
  varRefs : ∀ x ∈ s.varRefs, RefOK s.next x.2
  nodePts : ∀ x ∈ s.nodePts, RefOK s.next x
  constRefs : ∀ x ∈ s.constRefs, RefOK s.next x.2
  sources : ∀ row ∈ s.sources, RefOK s.next row.1 ∧ ∀ st ∈ row.2, st + 140604 ≤ s.next
  constants : ∀ d ∈ s.constants, RefOK s.next d.2.1 ∧ d.2.2 + 1 ≤ s.next ∧ 18 ≤ d.1
  operations : ∀ op ∈ s.operations, OpOK s.next 6 35134 mπ op

variable {p mπ}

theorem TrInv.mono {s : TrState} (h : TrInv p mπ s) {V : ℕ} (hV : s.next ≤ V) :
    p + 3 ≤ V ∧ (∀ x ∈ s.varRefs, RefOK V x.2) ∧ (∀ x ∈ s.nodePts, RefOK V x) ∧
      (∀ x ∈ s.constRefs, RefOK V x.2) ∧
      (∀ row ∈ s.sources, RefOK V row.1 ∧ ∀ st ∈ row.2, st + 140604 ≤ V) ∧
      (∀ d ∈ s.constants, RefOK V d.2.1 ∧ d.2.2 + 1 ≤ V ∧ 18 ≤ d.1) ∧
      (∀ op ∈ s.operations, OpOK V 6 35134 mπ op) :=
  ⟨by have := h.base; omega, fun x hx => (h.varRefs x hx).mono hV,
    fun x hx => (h.nodePts x hx).mono hV, fun x hx => (h.constRefs x hx).mono hV,
    fun row hrow => ⟨(h.sources row hrow).1.mono hV,
      fun st hst => by have := (h.sources row hrow).2 st hst; omega⟩,
    fun d hd => ⟨(h.constants d hd).1.mono hV, by have := (h.constants d hd).2.1; omega,
      (h.constants d hd).2.2⟩,
    fun op hop => (h.operations op hop).mono hV⟩

theorem OpOK.mono_w {V mα mμ mπ mα' mμ' mπ' : ℕ} {op : Operation} (h : OpOK V mα mμ mπ op)
    (hα : mα' ≤ mα) (hμ : mμ' ≤ mμ) (hπ : mπ' ≤ mπ) : OpOK V mα' mμ' mπ' op := by
  cases op with
  | add a b o s => exact ⟨h.1, h.2.1, h.2.2.1, by have := h.2.2.2; omega⟩
  | mul a b o s => exact ⟨h.1, h.2.1, h.2.2.1, by have := h.2.2.2; omega⟩
  | power a b c o s => exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by have := h.2.2.2.2; omega⟩

theorem RefOK.fresh {s V : ℕ} (h : s + 5 ≤ V) : RefOK V (s : ℤ) := Or.inr (by omega)

/-- The point reference of an explicit variable. -/
def trVarPt (k next : ℕ) (v : ℕ × VarKind) : ℤ := if IsInputVar k v then 5 * v.1 else next

/-- The natural start of an explicit variable. -/
def trVarStart (k : ℕ) (natInputs : Bool) (next : ℕ) (v : ℕ × VarKind) : Option ℕ :=
  if (!decide (IsInputVar k v) || natInputs) then
    some (if IsInputVar k v then next else next + 5) else none

theorem trVar_eq (k : ℕ) (natInputs : Bool) (s : TrState) (v : ℕ × VarKind) :
    trVar k natInputs s v = { s with
      next := s.next + varCost k natInputs v
      varRefs := s.varRefs ++ [(v.1, trVarPt k s.next v)]
      sources := s.sources ++ [(trVarPt k s.next v, trVarStart k natInputs s.next v)] } := by
  have := trVar_next k natInputs s v
  unfold trVar at this ⊢
  rw [← this]
  rfl

theorem trVarPt_ok {k p next : ℕ} (hk : 5 * k ≤ p) (hp : p + 3 ≤ next) (natInputs : Bool)
    (v : ℕ × VarKind) : RefOK (next + varCost k natInputs v) (trVarPt k next v) := by
  unfold trVarPt varCost
  by_cases hi : IsInputVar k v
  · simp only [hi, ite_true]
    refine Or.inr ?_
    have := hi.2
    have h5 : 5 * v.1 + 5 ≤ next + (if natInputs = true then 140604 else 0) := by
      have : next ≤ next + (if natInputs = true then 140604 else 0) := Nat.le_add_right _ _
      omega
    exact_mod_cast h5
  · simp only [hi, ite_false]
    exact RefOK.fresh (by omega)

theorem trVarStart_ok (k : ℕ) (natInputs : Bool) (next : ℕ) (v : ℕ × VarKind) :
    ∀ st ∈ trVarStart k natInputs next v, st + 140604 ≤ next + varCost k natInputs v := by
  intro st hst
  unfold trVarStart at hst
  unfold varCost
  by_cases hi : IsInputVar k v
  · cases natInputs
    · simp [hi] at hst
    · simp only [hi, decide_true, Bool.not_true, Bool.or_true, ite_true, Option.mem_def,
        Option.some.injEq] at hst
      rw [ite_eq_left_of_eq_true _ _ (eq_true hi), ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      omega
  · simp only [hi, decide_false, Bool.not_false, Bool.true_or, ite_true, ite_false,
      Option.mem_def, Option.some.injEq] at hst
    rw [ite_eq_right_of_eq_false _ _ (eq_false hi)]
    omega

theorem trVar_inv (k : ℕ) (hk : 5 * k ≤ p) (natInputs : Bool) {s : TrState} (h : TrInv p mπ s)
    (v : ℕ × VarKind) : TrInv p mπ (trVar k natInputs s v) := by
  have hle : s.next ≤ s.next + varCost k natInputs v := Nat.le_add_right _ _
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h.mono hle
  have hpt := trVarPt_ok hk h.base natInputs v
  rw [trVar_eq]
  refine ⟨h0, ?_, h2, h3, ?_, h5, h6⟩
  · intro x hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h1 x hx
    · exact hpt
  · intro row hrow
    simp only [List.mem_append, List.mem_singleton] at hrow
    rcases hrow with hrow | rfl
    · exact h4 row hrow
    · exact ⟨hpt, trVarStart_ok k natInputs s.next v⟩

theorem RefOK.getD {V : ℕ} {l : List ℤ} (h : ∀ x ∈ l, RefOK V x) (j : ℕ) :
    RefOK V (l.getD j (-4)) := by
  rw [List.getD_eq_getElem?_getD]
  cases hj : l[j]? with
  | none => exact RefOK.neg (by norm_num)
  | some x => exact h x (List.mem_of_getElem? hj)

theorem RefOK.lookup {V : ℕ} {α : Type} [DecidableEq α] {l : List (α × ℤ)}
    (h : ∀ x ∈ l, RefOK V x.2) (a : α) : RefOK V ((assocLookup l a).getD (-4)) := by
  unfold assocLookup
  cases hf : l.find? (fun e => decide (e.1 = a)) with
  | none => exact RefOK.neg (by norm_num)
  | some e => exact h e (List.mem_of_find?_eq_some hf)

theorem RefOK.lookup_some {V : ℕ} {α : Type} [DecidableEq α] {l : List (α × ℤ)}
    (h : ∀ x ∈ l, RefOK V x.2) {a : α} {r : ℤ} (hr : assocLookup l a = some r) :
    RefOK V r := by
  have := RefOK.lookup h a
  rwa [hr] at this

theorem trNode_inv (consts : List ℤ) {s : TrState} (h : TrInv p mπ s) (n : NatNode) :
    TrInv p mπ (trNode consts mπ s n) := by
  cases n with
  | var i =>
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
    refine ⟨h0, h1, ?_, h3, h4, h5, h6⟩
    intro x hx
    simp only [trNode, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact h2 x hx
    · exact RefOK.lookup h1 i
  | const c =>
    by_cases hc : IsNontrivial c
    · cases hl : assocLookup s.constRefs c with
      | some r =>
        have e : trNode consts mπ s (.const c) = { s with nodePts := s.nodePts ++ [r] } := by
          simp [trNode, hc, hl]
        rw [e]
        obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
        refine ⟨h0, h1, ?_, h3, h4, h5, h6⟩
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact h2 x hx
        · exact RefOK.lookup_some h3 hl
      | none =>
        have e : trNode consts mπ s (.const c) = { s with
            next := s.next + 5 + 1
            nodePts := s.nodePts ++ [(s.next : ℤ)]
            constRefs := s.constRefs ++ [(c, (s.next : ℤ))]
            constants := s.constants ++ [(18 + consts.idxOf c, (s.next : ℤ), s.next + 5)] } := by
          simp [trNode, hc, hl]
        rw [e]
        have hle : s.next ≤ s.next + 5 + 1 := by omega
        obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h.mono hle
        refine ⟨h0, h1, ?_, ?_, h4, ?_, h6⟩
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact h2 x hx
          · exact RefOK.fresh (by first | omega | (dsimp only; omega))
        · intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact h3 x hx
          · exact RefOK.fresh (by first | omega | (dsimp only; omega))
        · intro d hd
          simp only [List.mem_append, List.mem_singleton] at hd
          rcases hd with hd | rfl
          · exact h5 d hd
          · exact ⟨RefOK.fresh (by first | omega | (dsimp only; omega)), by first | omega | (dsimp only; omega), by omega⟩
    · have e : trNode consts mπ s (.const c) = { s with nodePts := s.nodePts ++ [trivialRef c] } := by
        simp [trNode, hc]
      rw [e]
      obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
      refine ⟨h0, h1, ?_, h3, h4, h5, h6⟩
      intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h2 x hx
      · refine RefOK.neg ?_
        unfold trivialRef
        split_ifs <;> norm_num
  | add a b =>
    simp only [trNode]
    have hle : s.next ≤ s.next + 5 + 6 := by omega
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h.mono hle
    refine ⟨h0, h1, ?_, h3, h4, h5, ?_⟩
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h2 x hx
      · exact RefOK.fresh (by first | omega | (dsimp only; omega))
    · intro op hop
      simp only [List.mem_append, List.mem_singleton] at hop
      rcases hop with hop | rfl
      · exact h6 op hop
      · exact ⟨RefOK.getD h2 a, RefOK.getD h2 b, RefOK.fresh (by first | omega | (dsimp only; omega)), by first | omega | (dsimp only; omega)⟩
  | mul a b =>
    simp only [trNode]
    have hle : s.next ≤ s.next + 5 + 35134 := by omega
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h.mono hle
    refine ⟨h0, h1, ?_, h3, h4, h5, ?_⟩
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h2 x hx
      · exact RefOK.fresh (by first | omega | (dsimp only; omega))
    · intro op hop
      simp only [List.mem_append, List.mem_singleton] at hop
      rcases hop with hop | rfl
      · exact h6 op hop
      · exact ⟨RefOK.getD h2 a, RefOK.getD h2 b, RefOK.fresh (by first | omega | (dsimp only; omega)), by first | omega | (dsimp only; omega)⟩
  | call a b c w =>
    simp only [trNode]
    have hle : s.next ≤ s.next + 5 + mπ := by omega
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h.mono hle
    refine ⟨h0, h1, ?_, h3, h4, h5, ?_⟩
    · intro x hx
      simp only [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h2 x hx
      · exact RefOK.fresh (by first | omega | (dsimp only; omega))
    · intro op hop
      simp only [List.mem_append, List.mem_singleton] at hop
      rcases hop with hop | rfl
      · exact h6 op hop
      · exact ⟨RefOK.getD h2 a, RefOK.getD h2 b, RefOK.getD h2 c, RefOK.fresh (by first | omega | (dsimp only; omega)),
          by first | omega | (dsimp only; omega)⟩

end Translate

theorem trState_inv (consts : List ℤ) (N : NatCircuit) (mode : OutputMode) (natInputs : Bool)
    (power : Option (ℕ × ℕ)) :
    TrInv (trParams N.inputCount mode) ((power.map Prod.snd).getD 0)
      (trState consts N mode natInputs power) := by
  have hk : 5 * N.inputCount ≤ trParams N.inputCount mode := by
    cases mode <;> simp [trParams]
  have h0 : TrInv (trParams N.inputCount mode) ((power.map Prod.snd).getD 0)
      ⟨trParams N.inputCount mode + 3, [], [], [], [], [], []⟩ :=
    ⟨le_rfl, by simp, by simp, by simp, by simp, by simp, by simp⟩
  have h1 : ∀ (l : List (ℕ × VarKind)) (s : TrState),
      TrInv (trParams N.inputCount mode) ((power.map Prod.snd).getD 0) s →
      TrInv (trParams N.inputCount mode) ((power.map Prod.snd).getD 0)
        (l.foldl (trVar N.inputCount natInputs) s) := by
    intro l
    induction l with
    | nil => exact fun s hs => hs
    | cons v l ih => exact fun s hs => ih _ (trVar_inv N.inputCount hk natInputs hs v)
  have h2 : ∀ (l : List NatNode) (s : TrState),
      TrInv (trParams N.inputCount mode) ((power.map Prod.snd).getD 0) s →
      TrInv (trParams N.inputCount mode) ((power.map Prod.snd).getD 0)
        (l.foldl (trNode consts ((power.map Prod.snd).getD 0)) s) := by
    intro l
    induction l with
    | nil => exact fun s hs => hs
    | cons n l ih => exact fun s hs => ih _ (trNode_inv consts hs n)
  exact h2 _ _ (h1 _ _ h0)

/-- **The translation is in range**, for any natural circuit, provided the operation templates
and the power recipe are well formed with witness counts at most the allocated blocks
(`140604`, `6`, `35134`, `1` for every scalar template, and the given count of the power
recipe). -/
theorem translate_inRange (templates recipes : List ExPoly) (consts : List ℤ) (N : NatCircuit)
    (mode : OutputMode) (natInputs : Bool) (power : Option (ℕ × ℕ))
    (hT : ∀ j, (getEx templates j).WF)
    (hν : (getEx templates 12).witnesses ≤ 140604) (hα : (getEx templates 1).witnesses ≤ 6)
    (hμ : (getEx templates 11).witnesses ≤ 35134)
    (hσ : ∀ h, (getEx templates (18 + h)).witnesses ≤ 1)
    (hπ : ∀ i w, power = some (i, w) → (getEx recipes i).WF ∧ (getEx recipes i).witnesses ≤ w) :
    (translate consts N mode natInputs power).InRange templates recipes := by
  have hI := trState_inv consts N mode natInputs power
  have hπ' : ((translate consts N mode natInputs power).powerCallee recipes).WF ∧
      ((translate consts N mode natInputs power).powerCallee recipes).witnesses ≤
        (power.map Prod.snd).getD 0 := by
    unfold ModelRecipe.powerCallee
    cases power with
    | none => exact ⟨ExPoly.empty_wf, Nat.zero_le _⟩
    | some iw => exact hπ iw.1 iw.2 rfl
  refine ⟨?_, ?_, hT _, hT _, hT _, hπ'.1, ?_, ?_, ?_, ?_⟩
  · have := hI.base
    show trParams N.inputCount mode ≤ (trState consts N mode natInputs power).next
    omega
  · intro i
    have := hI.base
    show (![trParams N.inputCount mode, trParams N.inputCount mode + 1,
      trParams N.inputCount mode + 2] : Fin 3 → ℕ) i < (trState consts N mode natInputs power).next
    fin_cases i <;> simp <;> omega
  · intro row hrow
    obtain ⟨h1, h2⟩ := hI.sources row hrow
    refine ⟨h1, fun st hst => ?_⟩
    have := h2 st hst
    show _ + (getEx templates 12).witnesses ≤ (trState consts N mode natInputs power).next
    omega
  · intro d hd
    obtain ⟨h1, h2, h3⟩ := hI.constants d hd
    refine ⟨hT _, h1, ?_⟩
    have := hσ (d.1 - 18)
    rw [Nat.add_sub_cancel' h3] at this
    show _ ≤ (trState consts N mode natInputs power).next
    omega
  · intro op hop
    exact (hI.operations op hop).mono_w hα hμ hπ'.2
  · refine ⟨RefOK.getD hI.nodePts _, ?_⟩
    cases mode with
    | value =>
      refine Or.inr ?_
      have := hI.base
      simp only [trParams] at this
      show ((5 * N.inputCount : ℕ) : ℤ) + 5 ≤ ((trState consts N .value natInputs power).next : ℤ)
      omega
    | zero => exact RefOK.neg (show (-1 : ℤ) < 0 by norm_num)

end ZInQ.Syntax
