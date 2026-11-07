import ZInQKernel.Compiler.NodeSkeleton.Sim.Macros

/-!
# The simulation of the packed-history construction

The tries and buckets of `Core.lean` answer like those of `NodeCheck/Trie.lean` and
`NodeCheck/Fast.lean` (both are characterized by `List.find?` and `List.filter`), and every
item of the kernel-friendly construction `NodeCheck.constructionK` is simulated by its
transcription.
-/

set_option linter.constructorNameAsVariable false

namespace ZInQ.Compiler.NodeSkeleton

open Natural NodeCheck Universal

/-! ### Tries -/

namespace LTrie

variable {α : Type}

/-- The root value and the two subtrees. -/
def view : LTrie α → Option α × LTrie α × LTrie α
  | leaf => (none, leaf, leaf)
  | node v l r => (v, l, r)

theorem find_node (v : Option α) (l r : LTrie α) (k : ℕ) :
    (node v l r).find k = if k = 0 then v else if k % 2 = 0 then l.find (k / 2)
      else r.find (k / 2) := by
  show cond (Nat.beq k 0) v (cond (Nat.beq (Nat.mod k 2) 0) (l.find (Nat.div k 2))
    (r.find (Nat.div k 2))) = _
  simp only [cond_eq_ite, Nat.beq_eq]
  rfl

theorem find_view (t : LTrie α) (k : ℕ) :
    t.find k = (node t.view.1 t.view.2.1 t.view.2.2).find k := by
  cases t with
  | leaf => rw [find_node]; simp only [view, ite_self]; split <;> rfl
  | node v l r => rfl

theorem ins_succ (f : ℕ) (t : LTrie α) (k : ℕ) (a : α) :
    t.ins (f + 1) k a =
      if k = 0 then node (some a) t.view.2.1 t.view.2.2
      else if k % 2 = 0 then node t.view.1 (t.view.2.1.ins f (k / 2) a) t.view.2.2
      else node t.view.1 t.view.2.1 (t.view.2.2.ins f (k / 2) a) := by
  cases t <;> simp only [ins, insStep, cond_eq_ite, Nat.beq_eq, view] <;> rfl

theorem find_ins (f : ℕ) (t : LTrie α) (k : ℕ) (a : α) (hk : k < f) (k' : ℕ) :
    (t.ins f k a).find k' = if k' = k then some a else t.find k' := by
  induction f generalizing t k k' with
  | zero => omega
  | succ f ih =>
    rw [find_view t k', ins_succ]
    generalize t.view = w
    obtain ⟨v, l, r⟩ := w
    simp only
    by_cases h0 : k = 0
    · subst h0
      simp only [ite_true, find_node]
      by_cases h' : k' = 0 <;> simp [h']
    · simp only [h0, ite_false]
      by_cases h2 : k % 2 = 0
      · simp only [h2, ite_true, find_node]
        by_cases h' : k' = 0
        · subst h'; simp [show (0 : ℕ) ≠ k by omega]
        · by_cases h2' : k' % 2 = 0
          · simp only [h', h2', ite_false, ite_true]
            rw [ih l (k / 2) (by omega)]
            congr 1
            apply propext; constructor <;> intro h <;> omega
          · simp only [h', h2', ite_false]
            simp only [show ¬ (k' = k) by omega, ite_false]
      · simp only [h2, ite_false, find_node]
        by_cases h' : k' = 0
        · subst h'; simp [show (0 : ℕ) ≠ k by omega]
        · by_cases h2' : k' % 2 = 0
          · simp only [h', h2', ite_false, ite_true]
            simp only [show ¬ (k' = k) by omega, ite_false]
          · simp only [h', h2', ite_false]
            rw [ih r (k / 2) (by omega)]
            congr 1
            apply propext; constructor <;> intro h <;> omega

theorem find_insert (t : LTrie α) (k : ℕ) (a : α) (k' : ℕ) :
    (t.insert k a).find k' = if k' = k then some a else t.find k' :=
  find_ins _ t k a (Nat.lt_succ_self k) k'

end LTrie

section Buckets

variable {β : Type}

theorem bucketsGo_eq' : ∀ (l : List (ℕ × β)) (t : LTrie (List β)),
    bucketsGo l t = l.foldl bucketIns t
  | [], _ => rfl
  | e :: l, t => by
    rw [List.foldl_cons, ← bucketsGo_eq' l (bucketIns t e)]
    show (match bucketIns t e with
      | .leaf => bucketsGo l .leaf
      | .node v a b => bucketsGo l (.node v a b)) = _
    split <;> rename_i h <;> rw [h]

theorem find_foldl_bucketIns' (l : List (ℕ × β)) (t : LTrie (List β)) (k : ℕ) :
    ((l.foldl bucketIns t).find k).getD [] =
      ((l.filter (·.1 == k)).map (·.2)).reverse ++ (t.find k).getD [] := by
  induction l generalizing t with
  | nil => rfl
  | cons e l ih =>
    rw [List.foldl_cons, ih, bucketIns, LTrie.find_insert]
    by_cases h : k = e.1
    · subst h; simp
    · simp [h, Ne.symm h]

theorem bucketGet_buckets' (l : List (ℕ × β)) (k : ℕ) :
    bucketGet (buckets l) k = (l.filter (·.1 == k)).map (·.2) := by
  rw [bucketGet, buckets, bucketsGo_eq', find_foldl_bucketIns']
  simp [LTrie.find]

/-- The buckets of both builders agree. -/
theorem bucketGet_eq (l : List (ℕ × β)) (k : ℕ) :
    NodeCheck.bucketGet (NodeCheck.buckets l) k = bucketGet (buckets l) k := by
  rw [NodeCheck.bucketGet_buckets, bucketGet_buckets']

end Buckets

theorem find_vwTrie' (vw : List (ℕ × ℕ × ℕ)) (i : ℕ) :
    (vwTrie vw).find i = (vw.find? fun e => e.1 == i).map (·.2) := by
  induction vw with
  | nil => rfl
  | cons e vw ih =>
    rw [vwTrie, List.foldr_cons, ← vwTrie, LTrie.find_insert, List.find?_cons]
    by_cases h : i = e.1
    · subst h; simp
    · have h' : (e.1 == i) = false := by simp [Ne.symm h]
      simp only [h', ih, h, ite_false]

theorem vwTrie_find_eq (vw : List (ℕ × ℕ × ℕ)) (i : ℕ) :
    (NodeCheck.vwTrie vw).find i = (vwTrie vw).find i := by
  rw [NodeCheck.find_vwTrie, find_vwTrie']

theorem pairsGo_eq' {β : Type} (zero : ℕ) (f : ℕ → RM.Instr → ℕ → List (ℕ × β))
    (g : ℕ → LInstr → ℕ → List (ℕ × β)) (hfg : ∀ i ins s, f i ins s = g i (toLI ins) s) :
    ∀ (i : ℕ) (p : List RM.Instr) (S : List ℕ),
      NodeCheck.pairsGo zero f i p S = pairsGo zero g i (p.map toLI) S
  | _, [], _ => rfl
  | i, ins :: p, S => by
    simp only [NodeCheck.pairsGo, List.map_cons, pairsGo, hfg, pairsGo_eq' zero f g hfg (i + 1) p]

theorem decHandle_eq (p : List RM.Instr) (zero : ℕ) (vw : List (ℕ × ℕ × ℕ)) (S : List ℕ)
    (j : ℕ) :
    NodeCheck.bucketGet (NodeCheck.buckets (NodeCheck.pairsGo zero
        (NodeCheck.decPairF zero (NodeCheck.vwTrie vw)) 0 p S)) j =
      bucketGet (buckets (pairsGo zero (decPairF zero (vwTrie vw)) 0 (p.map toLI) S)) j := by
  rw [pairsGo_eq' zero _ (decPairF zero (vwTrie vw)), bucketGet_eq]
  intro i ins s
  cases ins <;> simp [NodeCheck.decPairF, decPairF, toLI, vwTrie_find_eq]

theorem incHandle_eq (p : List RM.Instr) (zero : ℕ) (S : List ℕ) (j : ℕ) :
    NodeCheck.bucketGet (NodeCheck.buckets (NodeCheck.pairsGo zero NodeCheck.incPairF 0 p S)) j =
      bucketGet (buckets (pairsGo zero incPairF 0 (p.map toLI) S)) j := by
  rw [pairsGo_eq' zero _ incPairF, bucketGet_eq]
  intro i ins s
  cases ins <;> simp [NodeCheck.incPairF, incPairF, toLI]

theorem inHandle_eq (p : List RM.Instr) (zero : ℕ) (vw : List (ℕ × ℕ × ℕ)) (S : List ℕ)
    (j : ℕ) :
    NodeCheck.bucketGet (NodeCheck.buckets (NodeCheck.pairsGo zero
        (NodeCheck.inPairF zero (NodeCheck.vwTrie vw)) 0 p S)) j =
      bucketGet (buckets (pairsGo zero (inPairF zero (vwTrie vw)) 0 (p.map toLI) S)) j := by
  rw [pairsGo_eq' zero _ (inPairF zero (vwTrie vw)), bucketGet_eq]
  intro i ins s
  cases ins <;> simp [NodeCheck.inPairF, inPairF, toLI, vwTrie_find_eq]

/-! ### The items -/

section Items

variable {Hall : List ℕ}

theorem freshN_sim2 (n : ℕ) : Sim2 Hall id (NodeCheck.freshN n) (freshN n) := by
  induction n with
  | zero => exact Sim2.pure rfl
  | succ n ih =>
    exact Sim2.bindN fresh_sim2 fun _ => Sim2.bind Function.surjective_id ih fun _ => Sim2.pure rfl

theorem seqConcat_sim2 : ∀ {ms : List (FM (List FForm))} {ms' : List (HP (List LForm))},
    List.Forall₂ (Sim2 Hall (List.map toL)) ms ms' →
      Sim2 Hall (List.map toL) (NodeCheck.seqConcat ms) (seqConcat ms')
  | [], [], .nil => Sim2.pure rfl
  | _ :: _, _ :: _, .cons h hs =>
    Sim2.bind (map_surj toL_surj) h fun _ => Sim2.bind (map_surj toL_surj) (seqConcat_sim2 hs)
      fun _ => Sim2.pure (List.map_append ..)

theorem appendM_sim2 {m₁ m₂ : FM (List FForm)} {m₁' m₂' : HP (List LForm)}
    (h₁ : Sim2 Hall (List.map toL) m₁ m₁') (h₂ : Sim2 Hall (List.map toL) m₂ m₂') :
    Sim2 Hall (List.map toL) (NodeCheck.appendM m₁ m₂) (appendM m₁' m₂') :=
  Sim2.bind (map_surj toL_surj) h₁ fun _ => Sim2.bind (map_surj toL_surj) h₂ fun _ =>
    Sim2.pure (List.map_append ..)

theorem registerMasks_sim2 (K D T F Rj Nj : ℕ) :
    Sim2 Hall (List.map toL) (NodeCheck.registerMasks K D T F Rj Nj)
      (registerMasks K D T F Rj Nj) := by
  unfold NodeCheck.registerMasks registerMasks
  apply seqM_sim2 toL_surj
  sim2_tac

theorem registerEq_sim2 (B Rj ιj : ℕ) (decs incs : List ℕ) :
    Sim2 Hall toL (NodeCheck.registerEq B Rj ιj decs incs) (registerEq B Rj ιj decs incs) := by
  unfold NodeCheck.registerEq registerEq
  sim2_tac

theorem stateEq_sim2 (B Si e : ℕ) (ins : List ℕ) :
    Sim2 Hall toL (NodeCheck.stateEq B Si e ins) (stateEq B Si e ins) := by
  unfold NodeCheck.stateEq stateEq
  sim2_tac

theorem forall₂_map_same {α β γ : Type} {R : α → β → Prop} {l : List γ} {f : γ → α}
    {g : γ → β} (h : ∀ x, R (f x) (g x)) : List.Forall₂ R (l.map f) (l.map g) := by
  induction l with
  | nil => exact .nil
  | cons x l ih => exact .cons (h x) ih

theorem items1_sim2 (p : List RM.Instr) (a : List ℕ) (zero q c K B T : ℕ) :
    Sim2 Hall (List.map toL) (NodeCheck.items1 p a zero q c K B T)
      (items1 (p.map toLI) a zero q c K B T) := by
  unfold NodeCheck.items1 items1
  rw [List.length_map]
  apply seqM_sim2 toL_surj
  refine forall₂_append ?_ (forall₂_map_same fun ai => lt_sim2 ai K)
  sim2_tac

theorem items2_sim2 (zero one K B T F D : ℕ) (S : List ℕ) :
    Sim2 Hall (List.map toL) (NodeCheck.items2 zero one K B T F D S)
      (items2 zero one K B T F D S) := by
  unfold NodeCheck.items2 items2
  apply seqM_sim2 toL_surj
  sim2_tac

theorem items3_sim2 (F : ℕ) (S : List ℕ) :
    Sim2 Hall (List.map toL) (NodeCheck.items3 F S) (items3 F S) :=
  seqM_sim2 toL_surj (forall₂_map_same fun x => mask_sim2 x F)

theorem items4_sim2 (r : ℕ) (zero K D T F : ℕ) (R N : List ℕ) :
    Sim2 Hall (List.map toL) (NodeCheck.items4 r zero K D T F R N) (items4 r zero K D T F R N) :=
  seqConcat_sim2 (forall₂_map_same fun _ => registerMasks_sim2 ..)

/-- The erasure of the results of item 5. -/
def erSB (r : List FForm × List (ℕ × ℕ × ℕ)) : List LForm × List (ℕ × ℕ × ℕ) :=
  (r.1.map toL, r.2)

theorem erSB_surj : Function.Surjective erSB := by
  intro r
  obtain ⟨l, hl⟩ := map_surj toL_surj r.1
  exact ⟨(l, r.2), by simp [erSB, hl]⟩

theorem subBranchesK_sim2 (zero : ℕ) (N : List ℕ) :
    ∀ (i : ℕ) (S : List ℕ) (p : List RM.Instr),
      Sim2 Hall erSB (NodeCheck.subBranchesK zero N i S p) (subBranchesK zero N i S (p.map toLI))
  | _, _, [] => Sim2.pure rfl
  | i, S, .inc _ _ :: rest => subBranchesK_sim2 zero N (i + 1) S.tail rest
  | i, S, .halt :: rest => subBranchesK_sim2 zero N (i + 1) S.tail rest
  | i, S, .dec j _ _ :: rest => by
    show Sim2 Hall erSB _ (subBranchesK zero N i S (.dec _ _ _ :: rest.map toLI))
    unfold NodeCheck.subBranchesK subBranchesK
    refine Sim2.bindN fresh_sim2 fun V => Sim2.bindN fresh_sim2 fun W => ?_
    refine Sim2.bind (map_surj toL_surj) (seqM_sim2 toL_surj ?_) fun fs => ?_
    · sim2_tac
    · exact Sim2.bind erSB_surj (subBranchesK_sim2 zero N (i + 1) S.tail rest) fun _ =>
        Sim2.pure (by simp [erSB])

theorem items6K_sim2 (p : List RM.Instr) (r : ℕ) (a : List ℕ) (zero B : ℕ) (R S : List ℕ)
    (vw : List (ℕ × ℕ × ℕ)) :
    Sim2 Hall (List.map toL) (NodeCheck.items6K p r a zero B R S vw)
      (items6K (p.map toLI) r a zero B R S vw) := by
  unfold NodeCheck.items6K items6K
  simp only [decHandle_eq, incHandle_eq]
  exact seqM_sim2 toL_surj (forall₂_map_same fun _ => registerEq_sim2 ..)

theorem items7Go_sim2 (zero one B : ℕ) (inB : NTrie (List ℕ)) (inB' : LTrie (List ℕ))
    (h : ∀ i, NodeCheck.bucketGet inB i = bucketGet inB' i) :
    ∀ (n i : ℕ) (S : List ℕ), List.Forall₂ (Sim2 Hall toL)
      (NodeCheck.items7Go zero one B inB n i S) (items7Go zero one B inB' n i S)
  | 0, _, _ => .nil
  | n + 1, i, S => by
    unfold NodeCheck.items7Go items7Go
    rw [h i]
    exact .cons (stateEq_sim2 ..) (items7Go_sim2 zero one B inB inB' h n (i + 1) S.tail)

theorem items7K_sim2 (p : List RM.Instr) (zero one B : ℕ) (S : List ℕ)
    (vw : List (ℕ × ℕ × ℕ)) :
    Sim2 Hall (List.map toL) (NodeCheck.items7K p zero one B S vw)
      (items7K (p.map toLI) zero one B S vw) := by
  unfold NodeCheck.items7K items7K
  rw [List.length_map]
  exact seqM_sim2 toL_surj (items7Go_sim2 _ _ _ _ _ (inHandle_eq p zero vw S) _ _ _)

theorem packedFormulasK_sim2 (p : List RM.Instr) (r : ℕ) (a : List ℕ)
    (zero one q c K B T F D : ℕ) (R N S : List ℕ) :
    Sim2 Hall (List.map toL) (NodeCheck.packedFormulasK p r a zero one q c K B T F D R N S)
      (packedFormulasK (p.map toLI) r a zero one q c K B T F D R N S) := by
  unfold NodeCheck.packedFormulasK packedFormulasK
  refine appendM_sim2 (items1_sim2 ..) (appendM_sim2 (items2_sim2 ..) (appendM_sim2
    (items3_sim2 ..) (appendM_sim2 (items4_sim2 ..)
      (Sim2.bind erSB_surj (subBranchesK_sim2 ..) fun sb => ?_))))
  exact appendM_sim2 (Sim2.pure rfl) (appendM_sim2 (items6K_sim2 ..) (items7K_sim2 ..))

theorem constructionK_sim2 (p : List RM.Instr) (r k : ℕ) :
    Sim2 Hall toL (NodeCheck.constructionK p r k) (constructionK (p.map toLI) r k) := by
  unfold NodeCheck.constructionK constructionK
  refine Sim2.bindN (constant_sim2 0) fun zero => Sim2.bindN (constant_sim2 1) fun one =>
    Sim2.bindN fresh_sim2 fun q => Sim2.bindN fresh_sim2 fun c => Sim2.bindN fresh_sim2 fun K =>
    Sim2.bindN fresh_sim2 fun B => Sim2.bindN fresh_sim2 fun T => Sim2.bindN fresh_sim2 fun F =>
    Sim2.bindN fresh_sim2 fun D => ?_
  refine Sim2.bind Function.surjective_id (freshN_sim2 r) fun R =>
    Sim2.bind Function.surjective_id (freshN_sim2 r) fun N => ?_
  rw [← List.length_map (f := toLI)]
  refine Sim2.bind Function.surjective_id (freshN_sim2 _) fun S => ?_
  exact Sim2.bind (map_surj toL_surj) (packedFormulasK_sim2 ..) fun φs =>
    Sim2.pure (by simp [toL, toLs_eq])

end Items

end ZInQ.Compiler.NodeSkeleton
