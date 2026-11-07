import ZInQKernel.Compiler.NodeSkeleton.Sim.Packed
import ZInQKernel.Compiler.NodeSkeleton.Check
import ZInQKernel.Compiler.NodeSkeleton.Static

/-!
# Chaining the chunks

The fast run is cut into pieces along its bind structure (`appendM_bind`, `items3_split`,
`seqConcat_split`, `subBranchesK_split`, `encodeList_split`); each piece is simulated by a
piece of the checking builder whose run from a pinned state is checked by the kernel
(`chunkOK`). `cut` passes from the pinned start state of a chunk to that of the next one,
`Rel.reset` changing the hubs and lanes of the later chunks.
-/

set_option linter.constructorNameAsVariable false

namespace ZInQ.Compiler.NodeSkeleton

open Natural NodeCheck Universal

/-! ### Monad laws and splitting -/

theorem FM.bind_assoc' {α β γ : Type} (m : FM α) (f : α → FM β) (g : β → FM γ) :
    (m >>= f) >>= g = m >>= fun a => f a >>= g := rfl

theorem FM.pure_bind' {α β : Type} (a : α) (f : α → FM β) : (pure a >>= f) = f a := rfl

theorem appendM_bind {γ : Type} (m₁ m₂ : FM (List FForm)) (k : List FForm → FM γ) :
    (NodeCheck.appendM m₁ m₂ >>= k) = (m₁ >>= fun a => m₂ >>= fun b => k (a ++ b)) := rfl

theorem seqM_append {α : Type} (l₁ l₂ : List (FM α)) :
    NodeCheck.seqM (l₁ ++ l₂) =
      (NodeCheck.seqM l₁ >>= fun a => NodeCheck.seqM l₂ >>= fun b => pure (a ++ b)) := by
  induction l₁ with
  | nil => rfl
  | cons m l₁ ih =>
    show (m >>= fun a => NodeCheck.seqM (l₁ ++ l₂) >>= fun as => pure (a :: as)) = _
    rw [ih]; rfl

theorem items3_split {γ : Type} (F : ℕ) (A B : List ℕ) (k : List FForm → FM γ) :
    (NodeCheck.items3 F (A ++ B) >>= k) =
      (NodeCheck.items3 F A >>= fun a => NodeCheck.items3 F B >>= fun b => k (a ++ b)) := by
  unfold NodeCheck.items3
  rw [List.map_append, seqM_append]; rfl

theorem seqConcat_append (l₁ l₂ : List (FM (List FForm))) :
    NodeCheck.seqConcat (l₁ ++ l₂) =
      (NodeCheck.seqConcat l₁ >>= fun a => NodeCheck.seqConcat l₂ >>= fun b => pure (a ++ b)) := by
  induction l₁ with
  | nil => rfl
  | cons m l₁ ih =>
    show (m >>= fun a => NodeCheck.seqConcat (l₁ ++ l₂) >>= fun b => pure (a ++ b)) = _
    rw [ih]
    show _ = ((m >>= fun a => NodeCheck.seqConcat l₁ >>= fun b => pure (a ++ b)) >>= _)
    simp only [FM.bind_assoc', FM.pure_bind', List.append_assoc]

theorem seqConcat_split {γ : Type} (l₁ l₂ : List (FM (List FForm))) (k : List FForm → FM γ) :
    (NodeCheck.seqConcat (l₁ ++ l₂) >>= k) =
      (NodeCheck.seqConcat l₁ >>= fun a => NodeCheck.seqConcat l₂ >>= fun b => k (a ++ b)) := by
  rw [seqConcat_append]; rfl

theorem drop_succ_tail {α : Type} (S : List α) (n : ℕ) : S.drop (n + 1) = S.tail.drop n := by
  cases S <;> simp

theorem subBranchesK_append (zero : ℕ) (N : List ℕ) :
    ∀ (p₁ p₂ : List RM.Instr) (i : ℕ) (S : List ℕ),
      NodeCheck.subBranchesK zero N i S (p₁ ++ p₂) =
        (NodeCheck.subBranchesK zero N i S p₁ >>= fun r₁ =>
          NodeCheck.subBranchesK zero N (i + p₁.length) (S.drop p₁.length) p₂ >>= fun r₂ =>
            pure (r₁.1 ++ r₂.1, r₁.2 ++ r₂.2))
  | [], p₂, i, S => by
    show _ = (NodeCheck.subBranchesK zero N i S p₂ >>= fun r₂ => pure (r₂.1, r₂.2))
    rfl
  | .inc j x :: rest, p₂, i, S => by
    show NodeCheck.subBranchesK zero N (i + 1) S.tail (rest ++ p₂) =
      (NodeCheck.subBranchesK zero N (i + 1) S.tail rest >>= _)
    rw [subBranchesK_append zero N rest p₂ (i + 1) S.tail, List.length_cons, drop_succ_tail,
      show i + (rest.length + 1) = i + 1 + rest.length by omega]
  | .halt :: rest, p₂, i, S => by
    show NodeCheck.subBranchesK zero N (i + 1) S.tail (rest ++ p₂) =
      (NodeCheck.subBranchesK zero N (i + 1) S.tail rest >>= _)
    rw [subBranchesK_append zero N rest p₂ (i + 1) S.tail, List.length_cons, drop_succ_tail,
      show i + (rest.length + 1) = i + 1 + rest.length by omega]
  | .dec j x y :: rest, p₂, i, S => by
    simp only [List.cons_append, NodeCheck.subBranchesK]
    rw [subBranchesK_append zero N rest p₂ (i + 1) S.tail, List.length_cons, drop_succ_tail,
      show i + (rest.length + 1) = i + 1 + rest.length by omega]
    simp only [FM.bind_assoc', FM.pure_bind', List.append_assoc, List.cons_append]

theorem subBranchesK_split {γ : Type} (zero : ℕ) (N : List ℕ) (p₁ p₂ : List RM.Instr) (i j : ℕ)
    (S S' : List ℕ) (hj : j = i + p₁.length) (hS : S' = S.drop p₁.length)
    (k : List FForm × List (ℕ × ℕ × ℕ) → FM γ) :
    (NodeCheck.subBranchesK zero N i S (p₁ ++ p₂) >>= k) =
      (NodeCheck.subBranchesK zero N i S p₁ >>= fun r₁ =>
        NodeCheck.subBranchesK zero N j S' p₂ >>= fun r₂ => k (r₁.1 ++ r₂.1, r₁.2 ++ r₂.2)) := by
  rw [subBranchesK_append, hj, hS]; rfl

theorem encodeList_append : ∀ (l₁ l₂ : List FForm),
    FForm.encodeList (l₁ ++ l₂) =
      (FForm.encodeList l₁ >>= fun a => FForm.encodeList l₂ >>= fun b => pure (a ++ b))
  | [], l₂ => rfl
  | f :: l₁, l₂ => by
    show (f.encode >>= fun e => FForm.encodeList (l₁ ++ l₂) >>= fun es => pure (e :: es)) = _
    rw [encodeList_append l₁ l₂]; rfl

theorem encodeList_split {γ : Type} (l₁ l₂ : List FForm) (k : List ℕ → FM γ) :
    (FForm.encodeList (l₁ ++ l₂) >>= k) =
      (FForm.encodeList l₁ >>= fun a => FForm.encodeList l₂ >>= fun b => k (a ++ b)) := by
  rw [encodeList_append]; rfl

theorem encode_and {γ : Type} (fs : List FForm) (k : ℕ → FM γ) :
    ((FForm.and fs).encode >>= k) = (FForm.encodeList fs >>= fun es =>
      NodeCheck.seqM (es.map NodeCheck.square) >>= fun sq => NodeCheck.addL sq >>= k) := rfl

/-! ### The prelude -/

/-- The prelude of the fast construction. -/
def preludeFM (m r : ℕ) : FM PreludeVal := do
  let zero ← NodeCheck.constant 0
  let one ← NodeCheck.constant 1
  let q ← NodeCheck.fresh
  let c ← NodeCheck.fresh
  let K ← NodeCheck.fresh
  let B ← NodeCheck.fresh
  let T ← NodeCheck.fresh
  let F ← NodeCheck.fresh
  let D ← NodeCheck.fresh
  let R ← NodeCheck.freshN r
  let N ← NodeCheck.freshN r
  let S ← NodeCheck.freshN m
  pure (zero, one, q, c, K, B, T, F, D, R, N, S)

theorem constructionK_eq (p : RM.Program) (r k : ℕ) {γ : Type} (g : FForm → FM γ) :
    (NodeCheck.constructionK p r k >>= g) = (preludeFM p.length r >>= fun v =>
      NodeCheck.packedFormulasK p r (List.range k) v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2.1
        v.2.2.2.2.2.1 v.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.2.2.1
        v.2.2.2.2.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.2.2.2.2 >>= fun φs => g (.and φs)) := by
  simp only [NodeCheck.constructionK, preludeFM, FM.bind_assoc', FM.pure_bind']

theorem preludeFM_sim2 {Hall : List ℕ} (m r : ℕ) :
    Sim2 Hall id (preludeFM m r) (preludeHP m r) := by
  unfold preludeFM preludeHP
  refine Sim2.bindN (constant_sim2 0) fun zero => Sim2.bindN (constant_sim2 1) fun one =>
    Sim2.bindN fresh_sim2 fun q => Sim2.bindN fresh_sim2 fun c => Sim2.bindN fresh_sim2 fun K =>
    Sim2.bindN fresh_sim2 fun B => Sim2.bindN fresh_sim2 fun T => Sim2.bindN fresh_sim2 fun F =>
    Sim2.bindN fresh_sim2 fun D => ?_
  exact Sim2.bind Function.surjective_id (freshN_sim2 r) fun R =>
    Sim2.bind Function.surjective_id (freshN_sim2 r) fun N =>
    Sim2.bind Function.surjective_id (freshN_sim2 m) fun S => Sim2.pure rfl

theorem fastNodesRevK_bind (p : RM.Program) (r k : ℕ) :
    fastNodesRevK p r k =
      ((NodeCheck.constructionK p r k >>= fun φ => φ.encode) (FState.init k)).2.rev := by
  unfold fastNodesRevK
  rw [FM.bind_apply]

/-! ### Cutting at chunk boundaries -/

section Cut

variable {Hall : List ℕ}

/-- From the end of a chunk to the pinned start state of the next one. -/
theorem Rel.reset {Hf Hf' : List ℕ} {Ff Ff' : ℕ → List ℕ} {t : FState} {h sc : HState}
    (hr : Rel Hall Hf Ff t h) (he : EndRel h sc) (codes hubs : List ℕ) (lanes : List (List ℕ))
    (hH : Hf = hubs ++ Hf') (hF : ∀ ℓ, Ff ℓ = lanes.getD ℓ [] ++ Ff' ℓ)
    (hL : ∀ e ∈ Hf', sc.lim ≤ e / 8) :
    Rel Hall Hf' Ff' t (sc.withOracle codes hubs lanes) := by
  have hrem : ∀ ℓ, remL Ff' (sc.withOracle codes hubs lanes) ℓ = remL Ff h ℓ := by
    intro ℓ
    simp only [remL, HState.withOracle, he.lanes ℓ, List.nil_append, hF ℓ]
  refine ⟨?_, ?_, hr.lenRev, hr.table, hr.nodup, hr.child, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hL, ?_,
    ?_, ?_, hr.sorted⟩
  · show sc.len = t.len; rw [← he.len, hr.len]
  · show sc.next = t.next; rw [← he.next, hr.next]
  · show sc.adds = _; rw [← he.adds, hr.adds]
  · show sc.muls = _; rw [← he.muls, hr.muls]
  · intro c; show constFind _ sc.consts = _; rw [← he.consts, hr.consts]
  · intro e hm; show ∃ n, _; exact hr.hot e (by rw [he.hot]; exact hm)
  · exact he.win.trans hr.win
  · exact he.lim
  · show hubs ++ Hf' = Hall.filter fun e => sc.len ≤ e / 8
    rw [← hH, ← he.len, ← hr.hubs, he.hubs, List.nil_append]
  · intro ℓ; rw [hrem]; exact hr.laneNodup ℓ
  · intro ℓ; rw [hrem]; exact hr.laneLabel ℓ
  · intro j n hj hn hf ℓ; rw [hrem]; exact hr.hist j n hj hn hf ℓ

/-- **The cut**: a chunk checked by the kernel carries the relation from the pinned start state
of the chunk to that of the next one. -/
theorem cut {α β γ : Type} {er : α → β} {m : FM α} {m' : HP β} (hs : Sim2 Hall er m m')
    {beq : β → β → Bool} (hb : ∀ a b, beq a b = true → a = b)
    {Hf Hf' : List ℕ} {Ff Ff' : ℕ → List ℕ} {t : FState} {st sc : HState} {v : β}
    (hr : Rel Hall Hf Ff t st) (hc : chunkOK beq (m' st) sc v = true)
    (codes hubs : List ℕ) (lanes : List (List ℕ))
    (hH : Hf = hubs ++ Hf') (hF : ∀ ℓ, Ff ℓ = lanes.getD ℓ [] ++ Ff' ℓ)
    (hL : ∀ e ∈ Hf', sc.lim ≤ e / 8) {f : α → FM γ} {P : γ × FState → Prop}
    (hk : ∀ a, er a = v → ∀ t', Rel Hall Hf' Ff' t' (sc.withOracle codes hubs lanes) →
      P (f a t')) : P ((m >>= f) t) := by
  obtain ⟨h1, h2⟩ := chunkOK_sound hb hc
  obtain ⟨e1, r1⟩ := hs.run Hf Ff t st hr h2.ok
  rw [FM.bind_apply]
  exact hk _ (e1.trans h1) _ (r1.reset h2 codes hubs lanes hH hF hL)

/-- The last chunk: the counts of the final node list. -/
theorem cut_end {α β : Type} {er : α → β} {m : FM α} {m' : HP β} (hs : Sim2 Hall er m m')
    {beq : β → β → Bool} (hb : ∀ a b, beq a b = true → a = b)
    {Hf : List ℕ} {Ff : ℕ → List ℕ} {t : FState} {st sc : HState} {v : β}
    (hr : Rel Hall Hf Ff t st) (hc : chunkOK beq (m' st) sc v = true) :
    countKind .add (m t).2.rev = sc.adds ∧ countKind .mul (m t).2.rev = sc.muls := by
  obtain ⟨h1, h2⟩ := chunkOK_sound hb hc
  obtain ⟨-, r1⟩ := hs.run Hf Ff t st hr h2.ok
  exact ⟨r1.adds.symm.trans h2.adds, r1.muls.symm.trans h2.muls⟩

end Cut

theorem map_toL_inj {a : List FForm} {v : List LForm} (h : a.map toL = v) : a = ofLs v := by
  subst h
  induction a with
  | nil => rfl
  | cons f a ih =>
    show f :: a = ofL (toL f) :: ofLs (a.map toL)
    rw [ofL_toL, ← ih]

/-! ### The data of the chunks -/

/-- The hubs of the chunks after chunk `c`. -/
def hubsAfter (hubsData : List (List ℕ)) (c : ℕ) : List ℕ := (hubsData.drop (c + 1)).flatten

/-- The entries of lane `ℓ` in the chunks after chunk `c`. -/
def lanesAfter (lanesData : List (List (List ℕ))) (c ℓ : ℕ) : List ℕ :=
  ((lanesData.drop (c + 1)).map fun ls => ls.getD ℓ []).flatten

theorem lanes_suffix (lanesData : List (List (List ℕ))) (c ℓ : ℕ) :
    ∃ pre, laneAll lanesData ℓ = pre ++ ((lanesData.drop c).map fun ls => ls.getD ℓ []).flatten := by
  refine ⟨((lanesData.take c).map fun ls => ls.getD ℓ []).flatten, ?_⟩
  rw [← List.flatten_append, ← List.map_append, List.take_append_drop]; rfl

theorem hubsAfter_succ (hd : List (List ℕ)) (c : ℕ) (x : List ℕ) (hlen : c + 1 < hd.length)
    (hx : hd.getD (c + 1) [] = x) : hubsAfter hd c = x ++ hubsAfter hd (c + 1) := by
  unfold hubsAfter
  rw [List.drop_eq_getElem_cons hlen, List.flatten_cons, ← hx, List.getD_eq_getElem _ _ hlen]

theorem lanesAfter_succ (ld : List (List (List ℕ))) (c : ℕ) (x : List (List ℕ))
    (hlen : c + 1 < ld.length) (hx : ld.getD (c + 1) [] = x) (ℓ : ℕ) :
    lanesAfter ld c ℓ = x.getD ℓ [] ++ lanesAfter ld (c + 1) ℓ := by
  unfold lanesAfter
  rw [List.drop_eq_getElem_cons hlen, List.map_cons, List.flatten_cons, ← hx,
    List.getD_eq_getElem _ _ hlen]

/-- The static facts of the pinned data. -/
structure DataOK (hubsData : List (List ℕ)) (lanesData : List (List (List ℕ)))
    (limsData : List ℕ) : Prop where
  sorted : sortedHubsB (hubsAll hubsData) = true
  lim : hubsLimB limsData hubsData = true
  first : firstHubGe 2 hubsData = true
  len : lanesLenB 5 lanesData = true
  lanes : ∀ ℓ, ℓ < 5 → laneOKB hubsData lanesData ℓ = true

theorem DataOK.hubSorted {hd : List (List ℕ)} {ld : List (List (List ℕ))} {lims : List ℕ}
    (h : DataOK hd ld lims) : HubSorted (hubsAll hd) := hubSorted_of h.sorted

theorem DataOK.hubsLim {hd : List (List ℕ)} {ld : List (List (List ℕ))} {lims : List ℕ}
    (h : DataOK hd ld lims) {c : ℕ} (hc : c < lims.length) :
    ∀ e ∈ hubsAfter hd c, lims.getD c 0 ≤ e / 8 :=
  hubsLimB_sound (hubSorted_of h.sorted) h.lim c hc

theorem DataOK.laneNodup {hd : List (List ℕ)} {ld : List (List (List ℕ))} {lims : List ℕ}
    (h : DataOK hd ld lims) (c ℓ : ℕ) :
    (((ld.drop c).map fun ls => ls.getD ℓ []).flatten).Nodup := by
  obtain ⟨pre, hpre⟩ := lanes_suffix ld c ℓ
  have : (laneAll ld ℓ).Nodup := by
    by_cases hℓ : ℓ < 5
    · exact laneNodup_of (h.lanes ℓ hℓ)
    · rw [laneAll_nil h.len (by omega)]; exact List.nodup_nil
  rw [hpre] at this
  exact (List.nodup_append.mp this).2.1

theorem DataOK.laneLabel {hd : List (List ℕ)} {ld : List (List (List ℕ))} {lims : List ℕ}
    (h : DataOK hd ld lims) (c ℓ : ℕ) :
    ∀ e ∈ ((ld.drop c).map fun ls => ls.getD ℓ []).flatten,
      ℓ < 8 ∧ 8 * (e / laneBase) + ℓ ∈ hubsAll hd := by
  intro e he
  obtain ⟨pre, hpre⟩ := lanes_suffix ld c ℓ
  have he' : e ∈ laneAll ld ℓ := by rw [hpre]; exact List.mem_append_right _ he
  by_cases hℓ : ℓ < 5
  · exact laneLabel_of (h.lanes ℓ hℓ) e he'
  · rw [laneAll_nil h.len (by omega)] at he'; simp at he'

theorem init_nodes : nodesOf (FState.init 2) = [.var 0, .var 1] := rfl

theorem init_mem {n : NatNode} (h : n ∈ nodesOf (FState.init 2)) : n = .var 0 ∨ n = .var 1 := by
  rw [init_nodes] at h; simpa using h

/-- **The relation at the start**: the initial fast state and the first pinned state. -/
theorem rel_init {hd : List (List ℕ)} {ld : List (List (List ℕ))} {lims : List ℕ}
    (h : DataOK hd ld lims) (codes : List ℕ) (hlims : 0 < lims.length) (hl2 : 2 ≤ lims.getD 0 0) :
    Rel (hubsAll hd) (hubsAfter hd 0) (lanesAfter ld 0) (FState.init 2)
      ((stInit (lims.getD 0 0)).withOracle codes (hd.getD 0 []) (ld.getD 0 [])) := by
  have hge := firstHubGe_sound (hubSorted_of h.sorted) h.first
  have hflag : ∀ j, j < 2 → flagOf (hubsAll hd) j = false := by
    intro j hj
    simp only [flagOf, decide_eq_false_iff_not, List.mem_map, not_exists, not_and]
    intro x hx hxj
    have := hge x hx; omega
  have hrem : ∀ ℓ, remL (lanesAfter ld 0) ((stInit (lims.getD 0 0)).withOracle codes (hd.getD 0 [])
      (ld.getD 0 [])) ℓ = ((ld.drop 0).map fun ls => ls.getD ℓ []).flatten := by
    intro ℓ
    cases ld with
    | nil => simp [remL, lanesAfter, HState.withOracle]
    | cons l ld => simp [remL, lanesAfter, HState.withOracle]
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, rfl, rfl, ?_, ?_, ?_, hl2, ?_, h.hubsLim hlims, ?_, ?_, ?_,
    h.hubSorted⟩
  · intro n hn
    show NTrie.find NTrie.leaf _ = _
    rw [NTrie.find_leaf, eq_comm, List.idxOf?_eq_none_iff]
    intro hm
    rcases init_mem hm with rfl | rfl <;> simp [tabled] at hn
  · intro i j n hi _ hn
    rcases init_mem (List.mem_of_getElem? hi) with rfl | rfl <;> simp [tabled] at hn
  · intro j n hj hn
    rcases init_mem (List.mem_of_getElem? hj) with rfl | rfl <;> simp [isOp] at hn
  · intro c
    show none = _
    rw [eq_comm, List.idxOf?_eq_none_iff, init_nodes]
    simp
  · intro e he; simp [HState.withOracle, stInit] at he
  · show [14, 4] <+: recsOf (hubsAll hd) [.var 1, .var 0]
    simp only [recsOf, List.length_cons, List.length_nil, hflag 0 (by omega), hflag 1 (by omega)]
    exact List.prefix_refl _
  · show hd.getD 0 [] ++ hubsAfter hd 0 = (hubsAll hd).filter fun e => 2 ≤ e / 8
    rw [List.filter_eq_self.mpr (fun e he => by simpa using hge e he)]
    cases hd with
    | nil => rfl
    | cons x hd => rfl
  · intro ℓ; rw [hrem]; exact h.laneNodup 0 ℓ
  · intro ℓ; rw [hrem]; exact h.laneLabel 0 ℓ
  · intro j n hj hn
    rcases init_mem (List.mem_of_getElem? hj) with rfl | rfl <;> simp [isOp] at hn

/-! ### Splitting with literal arguments, and the pieces -/

theorem items3_split' {γ : Type} (F s m s' n total : ℕ) (h1 : s + m = s') (h2 : m + n = total)
    (k : List FForm → FM γ) :
    (NodeCheck.items3 F (List.range' s total) >>= k) =
      (NodeCheck.items3 F (List.range' s m) >>= fun a =>
        NodeCheck.items3 F (List.range' s' n) >>= fun b => k (a ++ b)) := by
  subst h1 h2
  rw [← List.range'_append_1, items3_split]

theorem seqConcat_map_split {γ : Type} (g : ℕ → FM (List FForm)) (s m s' n total : ℕ)
    (h1 : s + m = s') (h2 : m + n = total) (k : List FForm → FM γ) :
    (NodeCheck.seqConcat ((List.range' s total).map g) >>= k) =
      (NodeCheck.seqConcat ((List.range' s m).map g) >>= fun a =>
        NodeCheck.seqConcat ((List.range' s' n).map g) >>= fun b => k (a ++ b)) := by
  subst h1 h2
  rw [← List.range'_append_1, List.map_append, seqConcat_split]

theorem subBranchesK_split' {γ : Type} (zero : ℕ) (N : List ℕ) (p p₁ p₂ : List RM.Instr)
    (i j : ℕ) (S S' : List ℕ) (hp : p = p₁ ++ p₂) (hj : j = i + p₁.length)
    (hS : S' = S.drop p₁.length) (k : List FForm × List (ℕ × ℕ × ℕ) → FM γ) :
    (NodeCheck.subBranchesK zero N i S p >>= k) =
      (NodeCheck.subBranchesK zero N i S p₁ >>= fun r₁ =>
        NodeCheck.subBranchesK zero N j S' p₂ >>= fun r₂ => k (r₁.1 ++ r₂.1, r₁.2 ++ r₂.2)) := by
  subst hp; exact subBranchesK_split zero N p₁ p₂ i j S S' hj hS k

theorem squares_split {γ : Type} (A B : List ℕ) (k : List ℕ → FM γ) :
    (NodeCheck.seqM ((A ++ B).map NodeCheck.square) >>= k) =
      (NodeCheck.seqM (A.map NodeCheck.square) >>= fun a =>
        NodeCheck.seqM (B.map NodeCheck.square) >>= fun b => k (a ++ b)) := by
  rw [List.map_append, seqM_append]; rfl

section Pieces

variable {Hall : List ℕ}

theorem items4_piece_sim2 (K D T F zero : ℕ) (R N l : List ℕ) :
    Sim2 Hall (List.map toL)
      (NodeCheck.seqConcat (l.map fun j => NodeCheck.registerMasks K D T F (R.getD j zero) (N.getD j zero)))
      (seqConcat (l.map fun j => registerMasks K D T F (R.getD j zero) (N.getD j zero))) :=
  seqConcat_sim2 (forall₂_map_same fun _ => registerMasks_sim2 ..)

theorem enc_piece_sim2 (v : List LForm) :
    Sim2 Hall id (FForm.encodeList (ofLs v)) (LForm.encodeList v) := by
  have := encodeList_sim2 (Hall := Hall) (ofLs v)
  rwa [toLs_ofLs] at this

theorem sq_piece_sim2 (v : List ℕ) :
    Sim2 Hall id (NodeCheck.seqM (v.map NodeCheck.square)) (seqM (v.map square)) :=
  (seqM_sim2 Function.surjective_id (forall₂_square v)).congr_er List.map_id_fun

end Pieces

theorem erSB_inj {a : List FForm × List (ℕ × ℕ × ℕ)} {v : List LForm} {w : List (ℕ × ℕ × ℕ)}
    (h : erSB a = (v, w)) : a = (ofLs v, w) := by
  obtain ⟨a1, a2⟩ := a
  simp only [erSB, Prod.mk.injEq] at h
  rw [map_toL_inj h.1, h.2]

/-! ### An opaque bind

Both the kernel and the elaborator unfold `Bind.bind` (an instance projection) before
comparing arguments, and then run the fast builder symbolically. The chaining below therefore
writes the binds it creates with `Seq`, a regular definition whose applications are compared
argument by argument.
-/

/-- `m >>= f`, as a regular definition. -/
@[irreducible] def Seq {α β : Type} (m : FM α) (f : α → FM β) : FM β := m >>= f

theorem seq_eq {α β : Type} (m : FM α) (f : α → FM β) : Seq m f = m >>= f := by
  unfold Seq; rfl

theorem cutS {Hall : List ℕ} {α β γ : Type} {er : α → β} {m : FM α} {m' : HP β}
    (hs : Sim2 Hall er m m') {beq : β → β → Bool} (hb : ∀ a b, beq a b = true → a = b)
    {Hf Hf' : List ℕ} {Ff Ff' : ℕ → List ℕ} {t : FState} {st sc : HState} {v : β}
    (hr : Rel Hall Hf Ff t st) (hc : chunkOK beq (m' st) sc v = true)
    (codes hubs : List ℕ) (lanes : List (List ℕ))
    (hH : Hf = hubs ++ Hf') (hF : ∀ ℓ, Ff ℓ = lanes.getD ℓ [] ++ Ff' ℓ)
    (hL : ∀ e ∈ Hf', sc.lim ≤ e / 8) {f : α → FM γ} {P : γ × FState → Prop}
    (hk : ∀ a, er a = v → ∀ t', Rel Hall Hf' Ff' t' (sc.withOracle codes hubs lanes) →
      P (f a t')) : P (Seq m f t) := by
  rw [seq_eq]; exact cut hs hb hr hc codes hubs lanes hH hF hL hk

theorem constructionK_seq (p : RM.Program) (r k : ℕ) {γ : Type} (g : FForm → FM γ) :
    (NodeCheck.constructionK p r k >>= g) = Seq (preludeFM p.length r) (fun v =>
      Seq (NodeCheck.packedFormulasK p r (List.range k) v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2.1
        v.2.2.2.2.2.1 v.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.2.2.1
        v.2.2.2.2.2.2.2.2.2.2.1 v.2.2.2.2.2.2.2.2.2.2.2) fun φs => g (.and φs)) := by
  simp only [seq_eq]; exact constructionK_eq p r k g

theorem appendM_seq {γ : Type} (m₁ m₂ : FM (List FForm)) (k : List FForm → FM γ) :
    Seq (NodeCheck.appendM m₁ m₂) k = Seq m₁ (fun a => Seq m₂ fun b => k (a ++ b)) := by
  simp only [seq_eq]; rfl

theorem seq_bind {α β γ : Type} (m : FM α) (f : α → FM β) (k : β → FM γ) :
    Seq (m >>= f) k = Seq m (fun a => Seq (f a) k) := by
  simp only [seq_eq]; rfl

theorem pure_seq {α γ : Type} (x : α) (k : α → FM γ) : Seq (pure x) k = k x := by
  simp only [seq_eq]; rfl

theorem items3_seq {γ : Type} (F s m s' n total : ℕ) (h1 : s + m = s') (h2 : m + n = total)
    (k : List FForm → FM γ) :
    Seq (NodeCheck.items3 F (List.range' s total)) k =
      Seq (NodeCheck.items3 F (List.range' s m)) (fun a =>
        Seq (NodeCheck.items3 F (List.range' s' n)) fun b => k (a ++ b)) := by
  simp only [seq_eq]; exact items3_split' F s m s' n total h1 h2 k

theorem seqConcat_seq {γ : Type} (g : ℕ → FM (List FForm)) (s m s' n total : ℕ)
    (h1 : s + m = s') (h2 : m + n = total) (k : List FForm → FM γ) :
    Seq (NodeCheck.seqConcat ((List.range' s total).map g)) k =
      Seq (NodeCheck.seqConcat ((List.range' s m).map g)) (fun a =>
        Seq (NodeCheck.seqConcat ((List.range' s' n).map g)) fun b => k (a ++ b)) := by
  simp only [seq_eq]; exact seqConcat_map_split g s m s' n total h1 h2 k

theorem subBranchesK_seq {γ : Type} (zero : ℕ) (N : List ℕ) (p p₁ p₂ : List RM.Instr)
    (i j : ℕ) (S S' : List ℕ) (hp : p = p₁ ++ p₂) (hj : j = i + p₁.length)
    (hS : S' = S.drop p₁.length) (k : List FForm × List (ℕ × ℕ × ℕ) → FM γ) :
    Seq (NodeCheck.subBranchesK zero N i S p) k =
      Seq (NodeCheck.subBranchesK zero N i S p₁) (fun r₁ =>
        Seq (NodeCheck.subBranchesK zero N j S' p₂) fun r₂ => k (r₁.1 ++ r₂.1, r₁.2 ++ r₂.2)) := by
  simp only [seq_eq]; exact subBranchesK_split' zero N p p₁ p₂ i j S S' hp hj hS k

theorem encode_and_seq (fs : List FForm) :
    (FForm.and fs).encode = Seq (FForm.encodeList fs) (fun es =>
      Seq (NodeCheck.seqM (es.map NodeCheck.square)) fun sq => NodeCheck.addL sq) := by
  simp only [seq_eq]; rfl

theorem encodeList_seq {γ : Type} (l₁ l₂ : List FForm) (k : List ℕ → FM γ) :
    Seq (FForm.encodeList (l₁ ++ l₂)) k =
      Seq (FForm.encodeList l₁) (fun a => Seq (FForm.encodeList l₂) fun b => k (a ++ b)) := by
  simp only [seq_eq]; exact encodeList_split l₁ l₂ k

theorem squares_seq {γ : Type} (A B : List ℕ) (k : List ℕ → FM γ) :
    Seq (NodeCheck.seqM ((A ++ B).map NodeCheck.square)) k =
      Seq (NodeCheck.seqM (A.map NodeCheck.square)) (fun a =>
        Seq (NodeCheck.seqM (B.map NodeCheck.square)) fun b => k (a ++ b)) := by
  simp only [seq_eq]; exact squares_split A B k

end ZInQ.Compiler.NodeSkeleton
