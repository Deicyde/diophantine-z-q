import ZInQKernel.Compiler.Translation.Soundness

/-!
# Natural solutions give rational witnesses

Let `ρ` be the translation of a well-formed natural circuit `𝒩` and `θ` an admissible
assignment, natural at the inputs if they carry natural constraints. The assignment `x` that
writes `ι(θ_i)` at the inputs, `ι(𝒩(θ))` at the output (value mode), the generator coordinates
at `g₀, g₁, g₂`, `ι(θ_v)` at the fresh point of every explicit witness and `ι(val_θ(j))` at the
fresh point of every node is well defined (distinct allocations are disjoint, and all
occurrences of a constant share one point and one value) and satisfies conditions 1–4 of the
relational form, and also the root equality in value mode, and in zero mode when `𝒩(θ) = 0`
(`translate_complete`).

(Blueprint: `compiler/translation/translation-completeness.md`.)
-/

namespace ZInQ.Translation

open Compiler.Natural Syntax

theorem refVal_natCast (g : Fin 3 → ℕ) (x : ℕ → ℚ) (q : ℕ) :
    refVal g x (q : ℤ) = pointAt x q := by
  funext i
  simp [refVal, evCode, pointRef_natCast, pointAt]

theorem refVal_negative_of_generator {g : Fin 3 → ℕ} {x : ℕ → ℚ}
    (h : x (g 0) = 1641 / 8 ∧ x (g 1) = -15465 / 4 ∧ x (g 2) = 87483 / 32) :
    refVal g x (-1) = iota 0 ∧ refVal g x (-2) = iota 1 ∧ refVal g x (-3) = iota (-1) := by
  obtain ⟨h1, h2, h3⟩ := pointRef_eval_generator g x ((generatorConstraints_eq_zero_iff _ _).2 h)
  exact ⟨h1.trans iota_zero.symm, h2.trans codeP0_eq_iota, h3.trans codeNegP0_eq_iota⟩

/-- The code written at a fresh point with the given identity. -/
noncomputable def slotVal (P N : NatCircuit) (θ : ℕ → ℤ) : Slot → Fin 5 → ℚ
  | .var i => iota (θ i)
  | .out => iota (circuitValue P N θ)
  | .node j => iota (nodeVal P N θ j)
  | .const c => iota c

/-- The generator coordinates at `g₀, g₁, g₂`, zero elsewhere. -/
def genAssign (g : Fin 3 → ℕ) (m : ℕ) : ℚ :=
  if m = g 0 then 1641 / 8 else if m = g 1 then -15465 / 4 else if m = g 2 then 87483 / 32 else 0

section

variable {templates recipes : List ExPoly} {scalarOf : ℤ → ExPoly} {r : ModelRecipe}
  {P N : NatCircuit} {value natIn : Bool} {V : ℕ}

/-- The rational witnesses of a natural solution. -/
noncomputable def TranslationShape.witness
    (S : TranslationShape templates recipes scalarOf r P N value natIn) (θ : ℕ → ℤ) :
    ℕ → ℚ :=
  writePoints (genAssign r.generator) (S.slots.map fun e => (e.1, slotVal P N θ e.2))

theorem TranslationShape.witness_slot (S : TranslationShape templates recipes scalarOf r P N value natIn)
    (θ : ℕ → ℤ) {q : ℕ} {s : Slot} (h : (q, s) ∈ S.slots) :
    refVal r.generator (S.witness θ) q = slotVal P N θ s := by
  rw [refVal_natCast]
  refine writePoints_point_of_consistent _ ?_ (List.mem_map.2 ⟨_, h, rfl⟩)
  refine List.Pairwise.map _ (fun e e' h => ?_) S.slots_sep
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr h

theorem TranslationShape.witness_generator
    (S : TranslationShape templates recipes scalarOf r P N value natIn) (θ : ℕ → ℤ) :
    S.witness θ (r.generator 0) = 1641 / 8 ∧ S.witness θ (r.generator 1) = -15465 / 4 ∧
      S.witness θ (r.generator 2) = 87483 / 32 := by
  have hm : ∀ m : Fin 3, S.witness θ (r.generator m) = genAssign r.generator (r.generator m) :=
    fun m => writePoints_of_not_mem _ _ fun e he => by
      obtain ⟨e', he', rfl⟩ := List.mem_map.1 he
      exact S.slots_gen e' he' m
  obtain ⟨h01, h02, h12⟩ := S.gen_distinct
  refine ⟨?_, ?_, ?_⟩
  · rw [hm 0]; simp [genAssign]
  · rw [hm 1]; simp [genAssign, Ne.symm h01]
  · rw [hm 2]; simp [genAssign, Ne.symm h02, Ne.symm h12]

/-- **Natural solutions give rational witnesses.** For an admissible `θ` (natural at the inputs
when they carry natural constraints), the assignment `S.witness θ` has the input codes `ι(θ_i)`,
the output code `ι(𝒩(θ))` in value mode, makes every node point the code of the node's value,
and satisfies conditions 1–4 of the relational form; it satisfies the root equality in value
mode, and in zero mode when `𝒩(θ) = 0`. -/
theorem translate_complete (S : TranslationShape templates recipes scalarOf r P N value natIn)
    (hwf : WellFormed P N V) (hsem : CalleeSemantics (getEx templates r.natural)
      (getEx templates r.addition) (getEx templates r.multiplication) scalarOf)
    (hπ : HasCall N → PowerValueSpec (powerCallee recipes r) P)
    {θ : ℕ → ℤ} (hθ : Admissible P N θ) (hin : natIn = true → ∀ i < N.inputCount, 0 ≤ θ i) :
    (∀ i < N.inputCount, refVal r.generator (S.witness θ) (5 * i) = iota (θ i)) ∧
      (value = true →
        refVal r.generator (S.witness θ) (5 * N.inputCount) = iota (circuitValue P N θ)) ∧
      (∀ j < N.nodes.length, refVal r.generator (S.witness θ) (S.pt j) = iota (nodeVal P N θ j)) ∧
      ModelHoldsExceptRoot templates recipes r (S.witness θ) ∧
      (value = true ∨ circuitValue P N θ = 0 →
        ModelHolds templates recipes r (S.witness θ)) := by
  set x := S.witness θ
  set g := r.generator
  have hgen := S.witness_generator θ
  have hneg := refVal_negative_of_generator hgen
  have hinput : ∀ i < N.inputCount, refVal g x (5 * i) = iota (θ i) := fun i hi => by
    have := S.witness_slot θ (S.slot_input i hi)
    exact_mod_cast this
  have hvar : ∀ v ∈ N.explicitVars, refVal g x (S.vref v.1) = iota (θ v.1) := fun v hv => by
    cases hk : v.2
    · have hlt := lt_of_input hwf.core hv hk
      rw [S.vref_input _ hlt]
      exact_mod_cast hinput _ hlt
    · obtain ⟨q, hq, hs⟩ := S.slot_var v hv hk
      rw [hq]
      exact S.witness_slot θ hs
  have hnode : ∀ j < N.nodes.length, refVal g x (S.pt j) = iota (nodeVal P N θ j) := by
    intro j hj
    have hrec := nodeVal_eq_nodeValue_of_wf P N θ hwf.core.args_lt hj
    by_cases hv : ∃ i, N.nodes[j] = .var i
    · obtain ⟨i, hi⟩ := hv
      rw [S.pt_var j hj i hi, hrec, hi]
      obtain ⟨v, hv, hvi⟩ := hwf.core.var_explicit i (hi ▸ List.getElem_mem hj)
      subst hvi
      exact hvar v hv
    by_cases hc : ∃ c, N.nodes[j] = .const c
    · obtain ⟨c, hc⟩ := hc
      rw [hrec, hc]
      simp only [nodeValue]
      by_cases h0 : c = 0
      · subst h0; rw [S.pt_zero j hj hc]; exact hneg.1
      by_cases h1 : c = 1
      · subst h1; rw [S.pt_one j hj hc]; exact hneg.2.1
      by_cases h2 : c = -1
      · subst h2; rw [S.pt_neg_one j hj hc]; exact hneg.2.2
      obtain ⟨q, hq, hs⟩ := S.slot_const j hj c hc ⟨h0, h1, h2⟩
      rw [hq]
      exact S.witness_slot θ hs
    push Not at hv hc
    obtain ⟨q, hq, hs⟩ := S.slot_node j hj hv hc
    rw [hq]
    exact S.witness_slot θ hs
  have hnat : ∀ v ∈ N.explicitVars, (natIn = true ∨ v.2 = VarKind.witness) → 0 ≤ θ v.1 := by
    intro v hv hn
    cases hk : v.2
    · rcases hn with hn | hn
      · exact hin hn _ (lt_of_input hwf.core hv hk)
      · rw [hk] at hn; cases hn
    · exact hθ.1 v hv hk
  have hexc : ModelHoldsExceptRoot templates recipes r x := by
    refine ⟨hgen, fun row hrow s hs => ?_, fun d hd => ?_, fun op hop => ?_⟩
    · obtain ⟨v, hv, hrv, hn⟩ := S.row_inv row hrow s hs
      rw [hrv, hvar v hv]
      refine (hsem.natural _).2 ⟨(θ v.1).toNat, ?_⟩
      rw [Int.toNat_of_nonneg (hnat v hv hn)]
    · obtain ⟨j, hj, c, hc, hnt, hdpt, hdS⟩ := S.const_inv d hd
      have hcv : nodeVal P N θ j = c := by
        rw [nodeVal_eq_nodeValue_of_wf P N θ hwf.core.args_lt hj, hc]; rfl
      rw [hdS, hneg.2.1, hdpt, hnode j hj, hcv]
      exact (hsem.scalar c (hwf.core.const_ge_two c (hc ▸ List.getElem_mem hj) hnt.1 hnt.2.1
        hnt.2.2) _).2 rfl
    · obtain ⟨j, hj, h⟩ := S.op_inv op hop
      have hrec := nodeVal_eq_nodeValue_of_wf P N θ hwf.core.args_lt hj
      have hargs := hwf.core.args_lt j hj
      rcases h with ⟨a, b, s, hn, rfl⟩ | ⟨a, b, s, hn, rfl⟩ | ⟨a, b, c, w, s, hn, rfl⟩
      · rw [hn] at hargs hrec
        simp only [NatNode.children, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at hargs
        simp only [OpHolds]
        rw [hnode a (by omega), hnode b (by omega), hnode j hj, hrec]
        exact (hsem.add _ _ _).2 rfl
      · rw [hn] at hargs hrec
        simp only [NatNode.children, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at hargs
        simp only [OpHolds]
        rw [hnode a (by omega), hnode b (by omega), hnode j hj, hrec]
        exact (hsem.mul _ _ _).2 rfl
      · rw [hn] at hargs hrec
        simp only [NatNode.children, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at hargs
        have hcall : HasCall N := ⟨a, b, c, w, hn ▸ List.getElem_mem hj⟩
        have hP := (hwf.power hcall).2.2.1
        have hw : w ∈ N.blocks := mem_blocks_of_getElem hj hn
        simp only [OpHolds]
        rw [hnode a (by omega), hnode b (by omega), hnode c (by omega), hnode j hj, hrec]
        refine (hπ hcall _ _ _ _).2 ⟨fun i => (θ (w + i)).toNat, ?_⟩
        simp only [nodeValue]
        change iota (callValue P θ (nodeVal P N θ a) (nodeVal P N θ b) (nodeVal P N θ c) w) = _
        rw [callValue]
        congr 1
        refine templateValue_congr_of_core hP fun i hi => ?_
        simp only [blockAssign, callAssign]
        split_ifs with h3 h4
        · rfl
        · rw [Int.toNat_of_nonneg (hθ.2 w hw _ h4)]
        · omega
  refine ⟨hinput, fun hv => ?_, hnode, hexc, fun hmode => ⟨hexc, ?_⟩⟩
  · have := S.witness_slot θ (S.slot_out hv)
    exact_mod_cast this
  · rw [S.root]
    simp only
    rw [hnode _ hwf.core.root_lt]
    rcases hmode with hv | h0
    · rw [ite_eq_left hv]
      have := S.witness_slot θ (S.slot_out hv)
      exact_mod_cast this.symm
    · cases value
      · simp only [Bool.false_eq_true, ite_false]
        rw [hneg.1]
        exact congrArg iota h0
      · rw [ite_eq_left rfl]
        have := S.witness_slot θ (S.slot_out rfl)
        exact_mod_cast this.symm

end

end ZInQ.Translation
