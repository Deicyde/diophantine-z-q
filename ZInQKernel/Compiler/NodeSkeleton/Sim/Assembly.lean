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

theorem FM.bind_pure' {α : Type} (m : FM α) : (m >>= fun a => pure a) = m := rfl

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

end ZInQ.Compiler.NodeSkeleton
