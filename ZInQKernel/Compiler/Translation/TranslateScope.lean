import ZInQKernel.Compiler.Translation.RecipeScope
import ZInQKernel.Compiler.Translation.TranslateShape

/-!
# Witness scope of the translated recipes

For a well-formed circuit, the formula of its translation has the witness-scope facts
(`translate_scopedIn`): its callees are well formed, its call blocks are the allocated blocks
(so pairwise disjoint and above the parameters), every variable of a point reference or a
generator atom avoids them, and every variable lies below the variable count. The callee witness
counts must be those the translation allocates (`140604`, `6`, `35134`, `1` and the witness count
of the power recipe).

(Blueprint: the witness-scope theorem of `syntax/language/builder-well-formed.md`, for the
model-evaluation translation.)
-/

namespace ZInQ.Translation

open Compiler.Natural Syntax

/-- A point reference that is negative, a parameter point, or an allocated point. -/
def RefGood (p : ℕ) (slots : List (ℕ × Slot)) (ρ : ℤ) : Prop :=
  ρ < 0 ∨ ∃ q : ℕ, ρ = q ∧ (q + 5 ≤ p ∨ ∃ sl, (q, sl) ∈ slots)

section

variable {consts : List ℤ} {N : NatCircuit} {mode : OutputMode} {natIn : Bool}
  {power : Option (ℕ × ℕ)} {P : NatCircuit} {V : ℕ}

theorem refGood_trVref (hwf : WellFormed P N V) {v : ℕ × VarKind} (hv : v ∈ N.explicitVars) :
    RefGood (trParams N.inputCount mode) (trRun consts N mode natIn power).2.slots
      (trVref consts N mode natIn power v.1) := by
  have hpk : 5 * N.inputCount ≤ trParams N.inputCount mode := by
    cases mode <;> simp [trParams]
  have h := trVref_spec (consts := consts) (mode := mode) (natIn := natIn) (power := power) hwf hv
  by_cases hI : IsInputVar N.inputCount v
  · right
    refine ⟨5 * v.1, by rw [h.1 hI]; push_cast; ring, Or.inl ?_⟩
    have := hI.2
    omega
  · obtain ⟨q, hq, hs⟩ := h.2.1 hI
    exact Or.inr ⟨q, hq, Or.inr ⟨_, hs⟩⟩

theorem refGood_trPt (hwf : WellFormed P N V) (j : ℕ) :
    RefGood (trParams N.inputCount mode) (trRun consts N mode natIn power).2.slots
      (trPt consts N mode natIn power j) := by
  rcases Nat.lt_or_ge j N.nodes.length with hj | hj
  · have hs := trPt_spec (consts := consts) (mode := mode) (natIn := natIn) (power := power) hwf hj
    generalize N.nodes[j] = n at hs
    cases n with
    | var i =>
      simp only [NodePt] at hs
      rw [hs]
      cases hl : assocLookup (trRun consts N mode natIn power).1.varRefs i with
      | none => exact Or.inl (by simp)
      | some r =>
        have hm := mem_of_assocLookup hl
        have hN := trRun_nodeInv consts N mode natIn power hwf.core.args_lt
        rw [hN.varRefs] at hm
        have hk : i ∈ N.explicitVars.map Prod.fst := by
          rw [← (trRun_varInv N mode natIn).keys]
          exact List.mem_map.2 ⟨_, hm, rfl⟩
        obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hk
        have := refGood_trVref (consts := consts) (natIn := natIn) (power := power) (mode := mode)
          hwf hv
        rwa [trVref_eq_of_mem hwf hm] at this
    | const c =>
      by_cases hc : IsNontrivial c
      · obtain ⟨q, hq, hs', -⟩ := hs.1 hc
        exact Or.inr ⟨q, hq, Or.inr ⟨_, hs'⟩⟩
      · rw [hs.2 hc]
        left
        unfold trivialRef
        split_ifs <;> norm_num
    | add a b =>
      obtain ⟨q, hq, hs', -⟩ := hs
      exact Or.inr ⟨q, hq, Or.inr ⟨_, hs'⟩⟩
    | mul a b =>
      obtain ⟨q, hq, hs', -⟩ := hs
      exact Or.inr ⟨q, hq, Or.inr ⟨_, hs'⟩⟩
    | call a b c w =>
      obtain ⟨q, hq, hs', -⟩ := hs
      exact Or.inr ⟨q, hq, Or.inr ⟨_, hs'⟩⟩
  · have hN := trRun_nodeInv consts N mode natIn power hwf.core.args_lt
    left
    rw [trPt, List.getD_eq_default _ _ (by rw [hN.len]; exact hj)]
    norm_num

theorem refGood_getD (hwf : WellFormed P N V) (a : ℕ) :
    RefGood (trParams N.inputCount mode) (trRun consts N mode natIn power).2.slots
      ((trRun consts N mode natIn power).1.nodePts.getD a (-4)) :=
  refGood_trPt hwf a

/-- Every point reference used by the translation is negative, a parameter point or an allocated
point. -/
theorem refGood_usedRefs (hwf : WellFormed P N V) :
    ∀ ρ ∈ usedRefs (translate consts N mode natIn power),
      RefGood (trParams N.inputCount mode) (trRun consts N mode natIn power).2.slots ρ := by
  have hN := trRun_nodeInv consts N mode natIn power hwf.core.args_lt
  intro ρ hρ
  simp only [usedRefs, List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
    List.not_mem_nil, or_false] at hρ
  rcases hρ with (((⟨row, hrow, rfl⟩ | rfl | ⟨d, hd, rfl⟩) | ⟨op, hop, hρ⟩) | rfl | rfl)
  · rw [translate_sources, hN.sources] at hrow
    obtain ⟨v, hv, hr, -⟩ := (trRun_varInv N mode natIn).row row hrow
    rw [← trVref_eq_of_mem (consts := consts) (power := power) hwf hr]
    exact refGood_trVref hwf hv
  · exact Or.inl (by norm_num)
  · rw [translate_constants] at hd
    obtain ⟨⟨e, he, q, hq, rfl⟩, -⟩ := hN.constants d hd
    obtain ⟨-, q', hq', hs, -⟩ := hN.constRefs e he
    rw [hq] at hq'
    exact Or.inr ⟨q, rfl, Or.inr ⟨_, by rw [show q = q' by exact_mod_cast hq']; exact hs⟩⟩
  · rw [translate_operations] at hop
    obtain ⟨j, n, q, hj, hp, hn, rfl, -⟩ := hN.ops op hop
    obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.1 hj
    have hq : RefGood (trParams N.inputCount mode) (trRun consts N mode natIn power).2.slots q := by
      have := refGood_trPt (consts := consts) (mode := mode) (natIn := natIn) (power := power)
        hwf j
      obtain ⟨hp', hpe⟩ := List.getElem?_eq_some_iff.1 hp
      rwa [trPt, List.getD_eq_getElem _ _ hp', hpe] at this
    generalize N.nodes[j] = n at hρ hn
    cases n with
    | add a b =>
      simp only [opFor, opRefs, List.mem_cons, List.not_mem_nil, or_false] at hρ
      rcases hρ with rfl | rfl | rfl
      · exact refGood_getD hwf a
      · exact refGood_getD hwf b
      · exact hq
    | mul a b =>
      simp only [opFor, opRefs, List.mem_cons, List.not_mem_nil, or_false] at hρ
      rcases hρ with rfl | rfl | rfl
      · exact refGood_getD hwf a
      · exact refGood_getD hwf b
      · exact hq
    | call a b c w =>
      simp only [opFor, opRefs, List.mem_cons, List.not_mem_nil, or_false] at hρ
      rcases hρ with rfl | rfl | rfl | rfl
      · exact refGood_getD hwf a
      · exact refGood_getD hwf b
      · exact refGood_getD hwf c
      · exact hq
    | _ => exact absurd hn id
  · rw [translate_rootEq]
    exact refGood_trPt hwf _
  · rw [translate_rootEq]
    cases mode
    · right
      exact ⟨5 * N.inputCount, rfl, Or.inl (by simp [trParams]; omega)⟩
    · exact Or.inl (by norm_num)

theorem translate_variableCount_eq :
    (translate consts N mode natIn power).variableCount = (trRun consts N mode natIn power).1.next := by
  rw [trRun_fst]; rfl

theorem translate_parameterCount_eq :
    (translate consts N mode natIn power).parameterCount = trParams N.inputCount mode := rfl

theorem translate_generator (m : Fin 3) :
    (translate consts N mode natIn power).generator m = trParams N.inputCount mode + m := by
  fin_cases m <;> simp [Syntax.translate]

/-- The call blocks of the translation are its allocated blocks, in the order of its
conjuncts. -/
theorem blocks_translate (hwf : WellFormed P N V) {templates recipes : List ExPoly}
    (hνw : (getEx templates 12).witnesses = 140604) (hαw : (getEx templates 1).witnesses = 6)
    (hμw : (getEx templates 11).witnesses = 35134)
    (hcw : ∀ c, NatNode.const c ∈ N.nodes → Nontrivial c →
      (getEx templates (18 + consts.idxOf c)).witnesses = 1)
    (hpw : ∀ i w, power = some (i, w) → (getEx recipes i).witnesses = w) :
    ((translate consts N mode natIn power).formula templates recipes).blocks =
      formulaBlocks ((power.map Prod.snd).getD 0) (trRun consts N mode natIn power).1 := by
  have hN := trRun_nodeInv consts N mode natIn power hwf.core.args_lt
  rw [blocks_formula, formulaBlocks, translate_sources, translate_constants, translate_operations]
  have hnat : (translate consts N mode natIn power).natural = 12 := rfl
  have hadd : (translate consts N mode natIn power).addition = 1 := rfl
  have hmul : (translate consts N mode natIn power).multiplication = 11 := rfl
  rw [hnat, hadd, hmul, hνw]
  congr 1
  · congr 1
    refine List.map_congr_left fun d hd => ?_
    obtain ⟨⟨e, he, q, hq, rfl⟩, -⟩ := hN.constants d hd
    obtain ⟨hn, -, -, -, -, j, hj, -⟩ := hN.constRefs e he
    obtain ⟨hj', hjn⟩ := List.getElem?_eq_some_iff.1 hj
    simp only [constBlk]
    rw [hcw e.1 (hjn ▸ List.getElem_mem hj') hn]
  · refine List.map_congr_left fun op _ => ?_
    cases op with
    | add a b o s => simp [opBlock, opBlk, hαw]
    | mul a b o s => simp [opBlock, opBlk, hμw]
    | power a b c o s =>
      simp only [opBlock, opBlk, powerCallee, Syntax.translate]
      rcases power with _ | ⟨i, w⟩
      · rfl
      · simp [hpw i w rfl]

theorem powerCallee_translate_wf {recipes : List ExPoly}
    (hr : ∀ i w, power = some (i, w) → (getEx recipes i).WF) :
    (powerCallee recipes (translate consts N mode natIn power)).WF := by
  unfold powerCallee
  simp only [Syntax.translate]
  rcases power with _ | ⟨i, w⟩
  · exact ExPoly.empty_wf
  · exact hr i w rfl

/-- **Witness scope of the translation.** -/
theorem translate_scopedIn (hwf : WellFormed P N V) {templates recipes : List ExPoly}
    (ht : ∀ τ ∈ templates, τ.WF) (hr : ∀ i w, power = some (i, w) → (getEx recipes i).WF)
    (hνw : (getEx templates 12).witnesses = 140604) (hαw : (getEx templates 1).witnesses = 6)
    (hμw : (getEx templates 11).witnesses = 35134)
    (hcw : ∀ c, NatNode.const c ∈ N.nodes → Nontrivial c →
      (getEx templates (18 + consts.idxOf c)).witnesses = 1)
    (hpw : ∀ i w, power = some (i, w) → (getEx recipes i).witnesses = w) :
    ScopedIn ((translate consts N mode natIn power).formula templates recipes)
      (translate consts N mode natIn power).parameterCount
      (translate consts N mode natIn power).variableCount := by
  have hN := trRun_nodeInv consts N mode natIn power hwf.core.args_lt
  have hal := hN.alloc
  have hge := hN.next_ge
  have hbl := blocks_translate (mode := mode) (natIn := natIn) hwf hνw hαw hμw hcw hpw
  have hmem : ∀ b ∈ ((translate consts N mode natIn power).formula templates recipes).blocks,
      b ∈ (trRun consts N mode natIn power).2.blocks := fun b hb => by
    rw [hbl] at hb; exact hN.perm.subset hb
  have hwfc := callees_wf_formula' ht (translate consts N mode natIn power)
    (powerCallee_translate_wf hr)
  -- A used coordinate is not in a block and lies below the variable count.
  have hfree : ∀ f ∈ ((translate consts N mode natIn power).formula templates recipes).freePolys,
      ∀ i ∈ f.vars, (∀ b ∈ (trRun consts N mode natIn power).2.blocks, ¬ InBlock b i) ∧
        i < (trRun consts N mode natIn power).1.next := by
    intro f hf i hi
    rcases vars_freePolys templates recipes _ hf hi with ⟨m, rfl⟩ | ⟨ρ, hρ, q, rfl, hq1, hq2⟩
    · rw [translate_generator]
      have := m.isLt
      refine ⟨fun b hb hin => ?_, by omega⟩
      have := (hal.block_range b hb).1
      unfold InBlock at hin
      omega
    · rcases refGood_usedRefs hwf _ hρ with hneg | ⟨q', hq', hgood⟩
      · exact absurd hneg (by omega)
      · obtain rfl : q = q' := by exact_mod_cast hq'
        rcases hgood with hp | ⟨sl, hs⟩
        · refine ⟨fun b hb hin => ?_, by omega⟩
          have := (hal.block_range b hb).1
          unfold InBlock at hin
          omega
        · refine ⟨fun b hb hin => ?_, by have := (hal.slot_range _ hs).2; simp only at this; omega⟩
          have := hal.slot_block _ hs b hb
          unfold InBlock at hin
          unfold IntervalDisjoint at this
          simp only at this
          omega
  refine ⟨⟨hwfc, ?_, fun f hf i hi ⟨b, hb, hin⟩ => (hfree f hf i hi).1 b (hmem b hb) hin⟩,
    fun b hb => ?_, fun i hi => ?_, ?_⟩
  · rw [hbl]
    have := hN.perm.pairwise_iff (R := fun b b' => IntervalDisjoint b.1 b.2 b'.1 b'.2)
      (fun h => by unfold IntervalDisjoint at h ⊢; omega) |>.2 hal.blocks_disj
    refine this.imp fun h i hi hi' => ?_
    unfold IntervalDisjoint at h
    unfold InBlock at hi hi'
    omega
  · have := (hal.block_range b (hmem b hb)).1
    rw [translate_parameterCount_eq]
    omega
  · rw [translate_variableCount_eq]
    rcases Formula.mem_vars_compile hwfc hi with ⟨f, hf, hif⟩ | ⟨b, hb, hin⟩
    · exact (hfree f hf i hif).2
    · have := (hal.block_range b (hmem b hb)).2
      unfold InBlock at hin
      omega
  · rw [translate_parameterCount_eq, translate_variableCount_eq]
    omega

end

end ZInQ.Translation
