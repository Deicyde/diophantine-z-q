import ZInQKernel.Compiler.Translation.Spec

/-!
# Every node point is the code of the node's value

Let `ρ` be the translation of a well-formed natural circuit `𝒩` (power template `𝒫`, power
recipe `π` with (PV) if `𝒩` has call nodes), and let `x` satisfy conditions 1–4 of the
relational form of `ρ`. If the inputs carry natural constraints or the input points are
canonical, there is an admissible `θ` such that every input point, every explicit variable point
and every node point is the code of its value: `ref(pt j)(x) = ι(val_θ(j))` (`translate_sound`).

The proof is the typing order of the manuscript: the natural guards type the explicit variables
(never intermediate sums or products); raw addition receives canonical codes; M types the
products; the generator equations and the scalar templates give the constants; a power call
gives the code of the power template's value at some private natural witnesses, which define
`θ` on the call's block. By well-formedness that block is read by no other node, so the values of
the earlier nodes do not change.

(Blueprint: `compiler/translation/translation-soundness.md`.)
-/

namespace ZInQ.Translation

open Compiler.Natural Syntax

/-! ### Codes of the three negative references -/

theorem codeP0_eq_iota : codeP0 = iota 1 := iota_one.symm

theorem codeNegP0_eq_iota : codeNegP0 = iota (-1) := by
  rw [iota_neg, iota_one]
  funext i
  fin_cases i <;> simp [negCode, codeNegP0] <;> ring

theorem refVal_negative {templates recipes : List ExPoly} {r : ModelRecipe} {x : ℕ → ℚ}
    (h : ModelHoldsExceptRoot templates recipes r x) :
    refVal r.generator x (-1) = iota 0 ∧ refVal r.generator x (-2) = iota 1 ∧
      refVal r.generator x (-3) = iota (-1) := by
  obtain ⟨h1, h2, h3⟩ := refVal_generator h
  exact ⟨h1.trans iota_zero.symm, h2.trans codeP0_eq_iota, h3.trans codeNegP0_eq_iota⟩

/-! ### Explicit variables and blocks -/

theorem eq_of_mem_explicitVars {N : NatCircuit} {m V : ℕ} (hwf : WellFormedCore N m V)
    {v v' : ℕ × VarKind} (hv : v ∈ N.explicitVars) (hv' : v' ∈ N.explicitVars) (h : v.1 = v'.1) :
    v = v' :=
  List.inj_on_of_nodup_map hwf.vars_nodup hv hv' h

/-- An explicit variable of kind input is an input `i < k`. -/
theorem lt_of_input {N : NatCircuit} {m V : ℕ} (hwf : WellFormedCore N m V)
    {v : ℕ × VarKind} (hv : v ∈ N.explicitVars) (hk : v.2 = VarKind.input) :
    v.1 < N.inputCount := by
  rw [← List.take_append_drop N.inputCount N.explicitVars, List.mem_append] at hv
  rcases hv with hv | hv
  · rw [hwf.inputs_first, List.mem_map] at hv
    obtain ⟨i, hi, rfl⟩ := hv
    simpa using hi
  · rw [hwf.later_witness v hv] at hk
    cases hk

/-- The input `i < k` is the explicit variable `(i, input)`. -/
theorem input_mem {N : NatCircuit} {m V : ℕ} (hwf : WellFormedCore N m V) {i : ℕ}
    (hi : i < N.inputCount) : (i, VarKind.input) ∈ N.explicitVars := by
  have : (i, VarKind.input) ∈ N.explicitVars.take N.inputCount := by
    rw [hwf.inputs_first]; simpa using hi
  exact List.mem_of_mem_take this

theorem mem_blocks_of_getElem {N : NatCircuit} {t : ℕ} (ht : t < N.nodes.length) {a b c w : ℕ}
    (h : N.nodes[t] = .call a b c w) : w ∈ N.blocks :=
  mem_blocks_iff.2 ⟨a, b, c, h ▸ List.getElem_mem ht⟩

/-- The blocks of two distinct call nodes `j < t` are disjoint. -/
theorem blockDisjoint_of_lt {N : NatCircuit} {m V : ℕ} (hwf : WellFormedCore N m V) {j t : ℕ}
    (hjt : j < t) (ht : t < N.nodes.length) {a b c w a' b' c' w' : ℕ}
    (hj : N.nodes[j] = .call a b c w) (htc : N.nodes[t] = .call a' b' c' w') :
    BlockDisjoint (w, m) (w', m) := by
  have hsplit : N.nodes = N.nodes.take t ++ N.nodes[t] :: N.nodes.drop (t + 1) := by
    rw [List.getElem_cons_drop, List.take_append_drop]
  have hbl := hwf.blocks_disjoint
  unfold NatCircuit.blocks at hbl
  rw [hsplit, List.filterMap_append, htc, List.filterMap_cons_some (by rfl),
    List.pairwise_append] at hbl
  refine hbl.2.2 w ?_ w' List.mem_cons_self
  rw [List.mem_filterMap]
  refine ⟨N.nodes[j], ?_, by rw [hj]⟩
  have hj' : j < (N.nodes.take t).length := by rw [List.length_take]; omega
  rw [show N.nodes[j] = (N.nodes.take t)[j] by rw [List.getElem_take]]
  exact List.getElem_mem hj'

/-- Changing `θ` on the block of call node `t` does not change the values of the earlier
nodes. -/
theorem nodeVal_update_block {P N : NatCircuit} {V : ℕ} (hwf : WellFormed P N V) {t : ℕ}
    (ht : t < N.nodes.length) {a b c w : ℕ} (htc : N.nodes[t] = .call a b c w)
    {θ θ' : ℕ → ℤ} (hout : ∀ i, ¬ InBlock (w, P.varCount - 3) i → θ' i = θ i) {j : ℕ}
    (hj : j < t) : nodeVal P N θ' j = nodeVal P N θ j := by
  have hw : w ∈ N.blocks := mem_blocks_of_getElem ht htc
  have hP := (hwf.power ⟨a, b, c, w, htc ▸ List.getElem_mem ht⟩).2.2.1
  rw [nodeVal_eq_take P N θ' hj, nodeVal_eq_take P N θ hj]
  congr 1
  refine nodeValues_congr (fun i hi => ?_) fun a' b' c' w' hc x y z => ?_
  · obtain ⟨v, hv, rfl⟩ := hwf.core.var_explicit i (List.mem_of_mem_take hi)
    exact hout _ (hwf.core.blocks_explicit w hw v hv)
  · obtain ⟨j', hj', hjc⟩ := List.mem_iff_getElem.1 hc
    rw [List.length_take] at hj'
    have hjc' : N.nodes[j'] = .call a' b' c' w' := by
      rw [← hjc, List.getElem_take]
    have hd := blockDisjoint_of_lt hwf.core (by omega) ht hjc' htc
    exact callValue_congr hP (fun i hi => hout i (hd i hi)) x y z

/-! ### Soundness -/

/-- The explicit variables needing a natural value: the witnesses, and the inputs when they carry
natural constraints. -/
def NeedsNat (natIn : Bool) (N : NatCircuit) (i : ℕ) : Prop :=
  ∃ v ∈ N.explicitVars, v.1 = i ∧ (natIn = true ∨ v.2 = VarKind.witness)

section

variable {templates recipes : List ExPoly} {scalarOf : ℤ → ExPoly} {r : ModelRecipe}
  {P N : NatCircuit} {value natIn : Bool} {V : ℕ}

/-- The typing of the explicit variables: each explicit variable point is a canonical code, of
a natural number when the variable needs one. -/
theorem explicit_typed (S : TranslationShape templates recipes scalarOf r P N value natIn)
    (hwf : WellFormed P N V) (hsem : CalleeSemantics (getEx templates r.natural)
      (getEx templates r.addition) (getEx templates r.multiplication) scalarOf)
    {x : ℕ → ℚ} (hx : ModelHoldsExceptRoot templates recipes r x)
    (hin : natIn = false → ∀ i < N.inputCount, ∃ c : ℤ, refVal r.generator x (5 * i) = iota c)
    {v : ℕ × VarKind} (hv : v ∈ N.explicitVars) :
    ∃ t : ℤ, refVal r.generator x (S.vref v.1) = iota t ∧ (NeedsNat natIn N v.1 → 0 ≤ t) := by
  by_cases hn : natIn = true ∨ v.2 = VarKind.witness
  · obtain ⟨s, hs⟩ := S.row v hv hn
    obtain ⟨n, hn'⟩ := (hsem.natural _).1 (hx.natural _ hs s rfl)
    exact ⟨n, hn', fun _ => Int.natCast_nonneg n⟩
  · push Not at hn
    have hnat : natIn = false := by simpa using hn.1
    have hk : v.2 = VarKind.input := by
      cases h : v.2
      · rfl
      · exact absurd h hn.2
    have hlt := lt_of_input hwf.core hv hk
    obtain ⟨c, hc⟩ := hin hnat v.1 hlt
    refine ⟨c, by rw [S.vref_input _ hlt]; exact_mod_cast hc, ?_⟩
    rintro ⟨v', hv', he, hn'⟩
    have := eq_of_mem_explicitVars hwf.core hv hv' he.symm
    subst this
    rw [hnat] at hn'
    rcases hn' with h | h
    · cases h
    · exact absurd h hn.2

/-- **Every node point is the code of the node's value.** Let `x` satisfy conditions 1–4 of the
relational form of the translation `ρ` of a well-formed circuit `𝒩`, under the callee semantics
and (PV) for the power recipe if `𝒩` has call nodes, and assume that the inputs carry natural
constraints or that the input points are canonical. Then some admissible `θ` makes every input
point, explicit variable point and node point the code of its value, with `θ_i ∈ ℕ` for the
inputs when they carry natural constraints. -/
theorem translate_sound (S : TranslationShape templates recipes scalarOf r P N value natIn)
    (hwf : WellFormed P N V) (hsem : CalleeSemantics (getEx templates r.natural)
      (getEx templates r.addition) (getEx templates r.multiplication) scalarOf)
    (hπ : HasCall N → PowerValueSpec (powerCallee recipes r) P)
    {x : ℕ → ℚ} (hx : ModelHoldsExceptRoot templates recipes r x)
    (hin : natIn = false → ∀ i < N.inputCount, ∃ c : ℤ, refVal r.generator x (5 * i) = iota c) :
    ∃ θ : ℕ → ℤ, Admissible P N θ ∧
      (∀ i < N.inputCount, refVal r.generator x (5 * i) = iota (θ i) ∧
        (natIn = true → 0 ≤ θ i)) ∧
      (∀ v ∈ N.explicitVars, refVal r.generator x (S.vref v.1) = iota (θ v.1)) ∧
      ∀ j < N.nodes.length, refVal r.generator x (S.pt j) = iota (nodeVal P N θ j) := by
  classical
  set g := r.generator
  set m := P.varCount - 3
  have hneg := refVal_negative hx
  -- The values of the explicit variables.
  let Good : ℕ → ℤ → Prop := fun i t =>
    refVal g x (S.vref i) = iota t ∧ (NeedsNat natIn N i → 0 ≤ t)
  let θ₀ : ℕ → ℤ := fun i => if h : ∃ t, Good i t then h.choose else 0
  have hθ₀ : ∀ v ∈ N.explicitVars, Good v.1 (θ₀ v.1) := fun v hv => by
    have h : ∃ t, Good v.1 t := explicit_typed S hwf hsem hx hin hv
    simp only [θ₀, dite_eq_left h]
    exact h.choose_spec
  -- The invariant along the node list.
  let Inv : ℕ → (ℕ → ℤ) → Prop := fun t θ =>
    (∀ v ∈ N.explicitVars, θ v.1 = θ₀ v.1) ∧
    (∀ j (hj : j < N.nodes.length), j < t → ∀ a b c w, N.nodes[j] = .call a b c w →
      ∀ i < m, 0 ≤ θ (w + i)) ∧
    (∀ j (hj : j < N.nodes.length), j < t → refVal g x (S.pt j) = iota (nodeVal P N θ j))
  have step : ∀ t (ht : t < N.nodes.length) θ, Inv t θ → ∃ θ', Inv (t + 1) θ' := by
    intro t ht θ ⟨hvar, hblk, hval⟩
    have hargs := hwf.core.args_lt t ht
    have hrec := nodeVal_eq_nodeValue_of_wf P N θ hwf.core.args_lt ht
    -- Nodes other than calls keep `θ`.
    suffices hnc : (∀ a b c w, N.nodes[t] ≠ .call a b c w) →
        refVal g x (S.pt t) = iota (nodeVal P N θ t) by
      by_cases hc : ∃ a b c w, N.nodes[t] = .call a b c w
      · obtain ⟨a, b, c, w, htc⟩ := hc
        rw [htc] at hargs hrec
        simp only [NatNode.children, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq_or_imp, forall_eq] at hargs
        have hcall : HasCall N := ⟨a, b, c, w, htc ▸ List.getElem_mem ht⟩
        have hP := hwf.power hcall
        obtain ⟨s, hs⟩ := S.op_call t ht a b c w htc
        have hop := hx.operations _ hs
        simp only [OpHolds] at hop
        rw [hval a (by omega) hargs.1, hval b (by omega) hargs.2.1,
          hval c (by omega) hargs.2.2] at hop
        obtain ⟨w', hw'⟩ := (hπ hcall _ _ _ _).1 hop
        let θ' : ℕ → ℤ := fun i => if h : w ≤ i ∧ i - w < m then (w' ⟨i - w, h.2⟩ : ℤ) else θ i
        have hout : ∀ i, ¬ InBlock (w, m) i → θ' i = θ i := fun i hi => by
          simp only [θ', InBlock] at hi ⊢
          rw [dite_eq_right (by omega)]
        have hold : ∀ j < t, nodeVal P N θ' j = nodeVal P N θ j := fun j hj =>
          nodeVal_update_block hwf ht htc hout hj
        have hw : w ∈ N.blocks := mem_blocks_of_getElem ht htc
        refine ⟨θ', fun v hv => ?_, fun j hj hjt a' b' c' w'' hjc i hi => ?_, fun j hj hjt => ?_⟩
        · rw [hout _ (hwf.core.blocks_explicit w hw v hv)]
          exact hvar v hv
        · rcases Nat.lt_or_ge j t with hjt' | hjt'
          · have hd := blockDisjoint_of_lt hwf.core hjt' ht hjc htc
            rw [hout _ (hd _ ⟨by simp, by simp; omega⟩)]
            exact hblk j hj hjt' a' b' c' w'' hjc i hi
          · obtain rfl : j = t := by omega
            rw [htc] at hjc
            cases hjc
            simp only [θ']
            rw [dite_eq_left ⟨by omega, by simp; omega⟩]
            exact Int.natCast_nonneg _
        · rcases Nat.lt_or_ge j t with hjt' | hjt'
          · rw [hold j hjt']
            exact hval j hj hjt'
          · obtain rfl : j = t := by omega
            rw [hw', nodeVal_eq_nodeValue_of_wf P N θ' hwf.core.args_lt ht, htc]
            simp only [nodeValue]
            change _ = iota (callValue P θ' (nodeVal P N θ' a) (nodeVal P N θ' b)
              (nodeVal P N θ' c) w)
            rw [hold a hargs.1, hold b hargs.2.1, hold c hargs.2.2, callValue]
            congr 1
            refine templateValue_congr_of_core hP.2.2.1 fun i hi => ?_
            simp only [blockAssign, callAssign]
            split_ifs with h3 h4
            · rfl
            · simp only [θ']
              rw [dite_eq_left ⟨by omega, by omega⟩]
              congr 2
              ext
              simp
            · omega
      · push Not at hc
        refine ⟨θ, hvar, fun j hj hjt a b c w hjc => ?_, fun j hj hjt => ?_⟩
        · rcases Nat.lt_or_ge j t with hjt' | hjt'
          · exact hblk j hj hjt' a b c w hjc
          · obtain rfl : j = t := by omega
            exact absurd hjc (hc a b c w)
        · rcases Nat.lt_or_ge j t with hjt' | hjt'
          · exact hval j hj hjt'
          · obtain rfl : j = t := by omega
            exact hnc hc
    intro hnc
    rw [hrec]
    generalize hn : N.nodes[t] = n at hargs hnc
    cases n with
    | var i =>
      rw [S.pt_var t ht i hn]
      obtain ⟨v, hv, rfl⟩ := hwf.core.var_explicit i (hn ▸ List.getElem_mem ht)
      simp only [nodeValue]
      rw [hvar v hv]
      exact (hθ₀ v hv).1
    | const c =>
      simp only [nodeValue]
      by_cases h0 : c = 0
      · subst h0; rw [S.pt_zero t ht hn]; exact hneg.1
      by_cases h1 : c = 1
      · subst h1; rw [S.pt_one t ht hn]; exact hneg.2.1
      by_cases h2 : c = -1
      · subst h2; rw [S.pt_neg_one t ht hn]; exact hneg.2.2
      have hc2 := hwf.core.const_ge_two c (hn ▸ List.getElem_mem ht) h0 h1 h2
      obtain ⟨d, hd, hdpt, hdS⟩ := S.pt_const t ht c hn ⟨h0, h1, h2⟩
      have := hx.constants d hd
      rw [hdS, hneg.2.1, hdpt] at this
      exact (hsem.scalar c hc2 _).1 this
    | add a b =>
      simp only [NatNode.children, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hargs
      obtain ⟨s, hs⟩ := S.op_add t ht a b hn
      have hop := hx.operations _ hs
      simp only [OpHolds] at hop
      rw [hval a (by omega) hargs.1, hval b (by omega) hargs.2] at hop
      exact (hsem.add _ _ _).1 hop
    | mul a b =>
      simp only [NatNode.children, List.mem_cons, List.not_mem_nil, or_false,
        forall_eq_or_imp, forall_eq] at hargs
      obtain ⟨s, hs⟩ := S.op_mul t ht a b hn
      have hop := hx.operations _ hs
      simp only [OpHolds] at hop
      rw [hval a (by omega) hargs.1, hval b (by omega) hargs.2] at hop
      exact (hsem.mul _ _ _).1 hop
    | call a b c w => exact absurd rfl (hnc a b c w)
  have hall : ∀ t ≤ N.nodes.length, ∃ θ, Inv t θ := by
    intro t
    induction t with
    | zero => exact fun _ => ⟨θ₀, fun _ _ => rfl, fun _ _ h => absurd h (Nat.not_lt_zero _),
        fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
    | succ t ih =>
      intro ht
      obtain ⟨θ, hθ⟩ := ih (by omega)
      exact step t (by omega) θ hθ
  obtain ⟨θ, hvar, hblk, hval⟩ := hall _ le_rfl
  refine ⟨θ, ⟨fun v hv hw => ?_, fun w hw i hi => ?_⟩, fun i hi => ?_, fun v hv => ?_,
    fun j hj => hval j hj hj⟩
  · rw [hvar v hv]
    exact (hθ₀ v hv).2 ⟨v, hv, rfl, Or.inr hw⟩
  · obtain ⟨a, b, c, hc⟩ := mem_blocks_iff.1 hw
    obtain ⟨j, hj, hjc⟩ := List.mem_iff_getElem.1 hc
    exact hblk j hj hj a b c w hjc i hi
  · have hv := input_mem hwf.core hi
    have := hθ₀ _ hv
    rw [hvar _ hv]
    refine ⟨?_, fun hn => this.2 ⟨_, hv, rfl, Or.inl hn⟩⟩
    have h1 := this.1
    rw [S.vref_input i hi] at h1
    exact_mod_cast h1
  · rw [hvar v hv]
    exact (hθ₀ v hv).1

end

end ZInQ.Translation
