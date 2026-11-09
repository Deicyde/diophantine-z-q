import ZInQKernel.Compiler.NodeCheck.Check

/-!
# A kernel-friendly form of the fast packed-history construction

The handles of items 6 and 7 (`incHandles`, `decHandles`, `inHandles`) scan the whole program
for every register and every state, and look up branch histories by `List.find?`; the lists
`S`, `R`, `a` are read by `List.getD`. Here the handles are read from buckets (tries from keys
to the lists of handles, in program order) filled in one pass over the program, the branch
histories from a trie, and `S` is walked in lockstep with the instructions. The resulting
construction `constructionK` is equal to `construction` (`constructionK_eq`).
-/

namespace ZInQ.Compiler.NodeCheck

open Natural RM

/-! ### Buckets -/

section Buckets

variable {β : Type}

/-- Push `e.2` onto the bucket of key `e.1`. -/
def bucketIns (t : NTrie (List β)) (e : ℕ × β) : NTrie (List β) :=
  t.insert e.1 (e.2 :: (t.find e.1).getD [])

/-- Fill the buckets with a list of keyed values, in order (each step forces the trie). -/
def bucketsGo : List (ℕ × β) → NTrie (List β) → NTrie (List β)
  | [], t => t
  | e :: l, t =>
    match bucketIns t e with
    | .leaf => bucketsGo l .leaf
    | .node v a b => bucketsGo l (.node v a b)

/-- The buckets of a list of keyed values. -/
def buckets (l : List (ℕ × β)) : NTrie (List β) := bucketsGo l .leaf

/-- The values of key `k`, in order. -/
def bucketGet (t : NTrie (List β)) (k : ℕ) : List β := ((t.find k).getD []).reverse

theorem bucketsGo_eq : ∀ (l : List (ℕ × β)) (t : NTrie (List β)), bucketsGo l t = l.foldl bucketIns t
  | [], _ => rfl
  | e :: l, t => by
    rw [List.foldl_cons, ← bucketsGo_eq l (bucketIns t e)]
    show (match bucketIns t e with
      | .leaf => bucketsGo l .leaf
      | .node v a b => bucketsGo l (.node v a b)) = _
    split <;> rename_i h <;> rw [h]

theorem find_foldl_bucketIns (l : List (ℕ × β)) (t : NTrie (List β)) (k : ℕ) :
    ((l.foldl bucketIns t).find k).getD [] =
      ((l.filter (·.1 == k)).map (·.2)).reverse ++ (t.find k).getD [] := by
  induction l generalizing t with
  | nil => rfl
  | cons e l ih =>
    rw [List.foldl_cons, ih, bucketIns, NTrie.find_insert]
    by_cases h : k = e.1
    · subst h; simp
    · simp [h, Ne.symm h]

theorem bucketGet_buckets (l : List (ℕ × β)) (k : ℕ) :
    bucketGet (buckets l) k = (l.filter (·.1 == k)).map (·.2) := by
  rw [bucketGet, buckets, bucketsGo_eq, find_foldl_bucketIns]
  simp

end Buckets

/-! ### Branch histories by a trie -/

/-- The trie of branch histories (the first entry of each index wins). -/
def vwTrie (vw : List (ℕ × ℕ × ℕ)) : NTrie (ℕ × ℕ) :=
  vw.foldr (fun e t => t.insert e.1 e.2) .leaf

theorem find_vwTrie (vw : List (ℕ × ℕ × ℕ)) (i : ℕ) :
    (vwTrie vw).find i = (vw.find? fun e => e.1 == i).map (·.2) := by
  induction vw with
  | nil => rfl
  | cons e vw ih =>
    rw [vwTrie, List.foldr_cons, ← vwTrie, NTrie.find_insert, List.find?_cons]
    by_cases h : i = e.1
    · subst h; simp
    · have h' : (e.1 == i) = false := by simp [Ne.symm h]
      simp only [h', ih, h, ite_false]

theorem lookupVW_eq (zero : ℕ) (vw : List (ℕ × ℕ × ℕ)) (i : ℕ) :
    lookupVW zero vw i = ((vwTrie vw).find i).getD (zero, zero) := by
  rw [lookupVW, find_vwTrie]

/-! ### Handles by buckets -/

theorem filter_map_eq_flatMap {α γ : Type} (l : List α) (q : α → Bool) (g : α → γ) :
    (l.filter q).map g = l.flatMap fun i => if q i then [g i] else [] := by
  induction l with
  | nil => rfl
  | cons x l ih => by_cases h : q x <;> simp [List.filter_cons, h, ih]

theorem getD_succ {α : Type} (S : List α) (i : ℕ) (z : α) :
    S.getD (i + 1) z = S.tail.getD i z := by
  cases S <;> simp

/-- A pass over the program in lockstep with `S`: the keyed values of every instruction
(`ins i Sᵢ`, `Sᵢ = S.getD i zero`). -/
def pairsGo {β : Type} (zero : ℕ) (f : ℕ → Instr → ℕ → List (ℕ × β)) :
    ℕ → List Instr → List ℕ → List (ℕ × β)
  | _, [], _ => []
  | i, ins :: p, S => f i ins (S.headD zero) ++ pairsGo zero f (i + 1) p S.tail

theorem pairsGo_eq {β : Type} (zero : ℕ) (f : ℕ → Instr → ℕ → List (ℕ × β)) :
    ∀ (p : List Instr) (i : ℕ) (S : List ℕ),
      pairsGo zero f i p S = (List.range p.length).flatMap fun i' =>
        match p[i']? with
        | some ins => f (i + i') ins (S.getD i' zero)
        | none => []
  | [], _, _ => rfl
  | ins :: p, i, S => by
    rw [pairsGo, pairsGo_eq zero f p (i + 1) S.tail, List.length_cons, List.range_succ_eq_map,
      List.flatMap_cons, List.flatMap_map]
    congr 1
    · cases S <;> simp
    · congr 1
      funext i'
      simp only [List.getElem?_cons_succ, getD_succ]
      rw [show i + 1 + i' = i + (i' + 1) by omega]

/-- Keyed values of `A_j`: `(j, Sᵢ)` for `pᵢ = inc(j, ·)`. -/
def incPairF (_ : ℕ) : Instr → ℕ → List (ℕ × ℕ)
  | .inc j _, s => [(j, s)]
  | _, _ => []

/-- Keyed values of `C_j`: `(j, Vᵢ)` for `pᵢ = dec(j, ·, ·)`. -/
def decPairF (zero : ℕ) (vwT : NTrie (ℕ × ℕ)) (i : ℕ) : Instr → ℕ → List (ℕ × ℕ)
  | .dec j _ _, _ => [(j, ((vwT.find i).getD (zero, zero)).1)]
  | _, _ => []

/-- Keyed values of `I_x`: `(x, Sᵢ)` for `pᵢ = inc(·, x)`, `(x, Vᵢ)` and `(y, Wᵢ)` for
`pᵢ = dec(·, x, y)`. -/
def inPairF (zero : ℕ) (vwT : NTrie (ℕ × ℕ)) (i : ℕ) : Instr → ℕ → List (ℕ × ℕ)
  | .inc _ x, s => [(x, s)]
  | .dec _ x y, _ => [(x, ((vwT.find i).getD (zero, zero)).1),
      (y, ((vwT.find i).getD (zero, zero)).2)]
  | .halt, _ => []

theorem incHandles_eq (p : Program) (zero : ℕ) (S : List ℕ) (j : ℕ) :
    incHandles p zero S j = bucketGet (buckets (pairsGo zero incPairF 0 p S)) j := by
  rw [bucketGet_buckets, pairsGo_eq, incHandles, filter_map_eq_flatMap, List.filter_flatMap,
    List.map_flatMap]
  congr 1
  funext i
  cases h : p[i]? with
  | none => simp [Packed.incOn, h]
  | some ins =>
    cases ins with
    | inc j' x =>
      by_cases hj : j' = j
      · subst hj; simp [Packed.incOn, h, incPairF]
      · simp [Packed.incOn, h, incPairF, hj]
    | dec j' x y => simp [Packed.incOn, h, incPairF]
    | halt => simp [Packed.incOn, h, incPairF]

theorem decHandles_eq (p : Program) (zero : ℕ) (vw : List (ℕ × ℕ × ℕ)) (S : List ℕ) (j : ℕ) :
    decHandles p zero vw j =
      bucketGet (buckets (pairsGo zero (decPairF zero (vwTrie vw)) 0 p S)) j := by
  rw [bucketGet_buckets, pairsGo_eq, decHandles, filter_map_eq_flatMap, List.filter_flatMap,
    List.map_flatMap]
  congr 1
  funext i
  cases h : p[i]? with
  | none => simp [Packed.decOn, h]
  | some ins =>
    cases ins with
    | dec j' x y =>
      by_cases hj : j' = j
      · subst hj; simp [Packed.decOn, h, decPairF, lookupVW_eq]
      · simp [Packed.decOn, h, decPairF, hj]
    | inc j' x => simp [Packed.decOn, h, decPairF]
    | halt => simp [Packed.decOn, h, decPairF]

theorem inHandles_eq (p : Program) (zero : ℕ) (S : List ℕ) (vw : List (ℕ × ℕ × ℕ)) (i : ℕ) :
    inHandles p zero S vw i =
      bucketGet (buckets (pairsGo zero (inPairF zero (vwTrie vw)) 0 p S)) i := by
  rw [bucketGet_buckets, pairsGo_eq, inHandles, List.filter_flatMap, List.map_flatMap]
  congr 1
  funext i'
  cases h : p[i']? with
  | none => simp [Packed.incTo, Packed.nzTo, Packed.zTo, h]
  | some ins =>
    cases ins with
    | inc j x =>
      by_cases hx : x = i
      · subst hx; simp [Packed.incTo, Packed.nzTo, Packed.zTo, h, inPairF]
      · simp [Packed.incTo, Packed.nzTo, Packed.zTo, h, inPairF, hx]
    | dec j x y =>
      by_cases hx : x = i <;> by_cases hy : y = i <;>
        simp [Packed.incTo, Packed.nzTo, Packed.zTo, h, inPairF, hx, hy, lookupVW_eq,
          List.filter_cons]
    | halt => simp [Packed.incTo, Packed.nzTo, Packed.zTo, h, inPairF]

/-! ### The construction -/

theorem headD_drop {α : Type} (S : List α) (i : ℕ) (z : α) : (S.drop i).headD z = S.getD i z := by
  induction S generalizing i with
  | nil => simp
  | cons x S ih => cases i <;> simp [ih]

/-- Item 5, walking `S` in lockstep with the instructions. -/
def subBranchesK (zero : ℕ) (N : List ℕ) :
    ℕ → List ℕ → List Instr → FM (List FForm × List (ℕ × ℕ × ℕ))
  | _, _, [] => pure ([], [])
  | i, S, .dec j _ _ :: rest => do
    let V ← fresh
    let W ← fresh
    let fs ← seqM [
      bitAnd V (S.headD zero) (N.getD j zero),
      do pure (.eq (S.headD zero) (← addL [V, W]))]
    let rest' ← subBranchesK zero N (i + 1) S.tail rest
    pure (fs ++ rest'.1, (i, V, W) :: rest'.2)
  | i, S, .inc _ _ :: rest => subBranchesK zero N (i + 1) S.tail rest
  | i, S, .halt :: rest => subBranchesK zero N (i + 1) S.tail rest

theorem subBranchesK_eq (zero : ℕ) (S N : List ℕ) :
    ∀ (p : List Instr) (i : ℕ), subBranchesK zero N i (S.drop i) p = subBranches zero S N i p
  | [], _ => rfl
  | ins :: p, i => by
    cases ins with
    | inc j x =>
      simp only [subBranchesK, subBranches, List.tail_drop, subBranchesK_eq zero S N p (i + 1)]
    | halt =>
      simp only [subBranchesK, subBranches, List.tail_drop, subBranchesK_eq zero S N p (i + 1)]
    | dec j x y =>
      simp only [subBranchesK, subBranches, List.tail_drop, headD_drop,
        subBranchesK_eq zero S N p (i + 1)]

/-- Item 6, with the handles read from buckets. -/
def items6K (p : Program) (r : ℕ) (a : List ℕ) (zero B : ℕ) (R S : List ℕ)
    (vw : List (ℕ × ℕ × ℕ)) : FM (List FForm) :=
  let decB := buckets (pairsGo zero (decPairF zero (vwTrie vw)) 0 p S)
  let incB := buckets (pairsGo zero incPairF 0 p S)
  seqM ((List.range r).map fun j =>
    registerEq B (R.getD j zero) (a.getD j zero) (bucketGet decB j) (bucketGet incB j))

theorem items6K_eq (p : Program) (r : ℕ) (a : List ℕ) (zero B : ℕ) (R S : List ℕ)
    (vw : List (ℕ × ℕ × ℕ)) : items6K p r a zero B R S vw = items6 p r a zero B R S vw := by
  simp only [items6K, items6, ← incHandles_eq, ← decHandles_eq]

/-- The formulas of item 7 for the states `i, …, i + n - 1`, walking `S` in lockstep. -/
def items7Go (zero one B : ℕ) (inB : NTrie (List ℕ)) : ℕ → ℕ → List ℕ → List (FM FForm)
  | 0, _, _ => []
  | n + 1, i, S =>
    stateEq B (S.headD zero) (bif i.beq 0 then one else zero) (bucketGet inB i) ::
      items7Go zero one B inB n (i + 1) S.tail

theorem items7Go_eq (zero one B : ℕ) (inB : NTrie (List ℕ)) (S : List ℕ) :
    ∀ (n i : ℕ), items7Go zero one B inB n i (S.drop i) = (List.range' i n).map fun i =>
      stateEq B (S.getD i zero) (if i = 0 then one else zero) (bucketGet inB i)
  | 0, _ => rfl
  | n + 1, i => by
    rw [items7Go, List.range'_succ, List.map_cons, List.tail_drop, items7Go_eq zero one B inB S n,
      headD_drop]
    congr 2
    simp only [cond_eq_ite, Nat.beq_eq]

/-- Item 7, with the handles read from buckets. -/
def items7K (p : Program) (zero one B : ℕ) (S : List ℕ) (vw : List (ℕ × ℕ × ℕ)) :
    FM (List FForm) :=
  let inB := buckets (pairsGo zero (inPairF zero (vwTrie vw)) 0 p S)
  seqM (items7Go zero one B inB p.length 0 S)

theorem items7K_eq (p : Program) (zero one B : ℕ) (S : List ℕ) (vw : List (ℕ × ℕ × ℕ)) :
    items7K p zero one B S vw = items7 p zero one B S vw := by
  have h := items7Go_eq zero one B (buckets (pairsGo zero (inPairF zero (vwTrie vw)) 0 p S)) S
    p.length 0
  rw [List.drop_zero] at h
  simp only [items7K, items7, h, List.range_eq_range', ← inHandles_eq]

/-- Items 1–7, kernel-friendly. -/
def packedFormulasK (p : Program) (r : ℕ) (a : List ℕ) (zero one q c K B T F D : ℕ)
    (R N S : List ℕ) : FM (List FForm) :=
  appendM (items1 p a zero q c K B T) <|
  appendM (items2 zero one K B T F D S) <|
  appendM (items3 F S) <|
  appendM (items4 r zero K D T F R N) do
    let sb ← subBranchesK zero N 0 S p
    appendM (pure sb.1) <|
    appendM (items6K p r a zero B R S sb.2) (items7K p zero one B S sb.2)

theorem packedFormulasK_eq (p : Program) (r : ℕ) (a : List ℕ) (zero one q c K B T F D : ℕ)
    (R N S : List ℕ) : packedFormulasK p r a zero one q c K B T F D R N S =
      packedFormulas p r a zero one q c K B T F D R N S := by
  have h := subBranchesK_eq zero S N p 0
  rw [List.drop_zero] at h
  simp only [packedFormulasK, packedFormulas, h, items6K_eq, items7K_eq]

/-- The fast packed-history construction, kernel-friendly. -/
def constructionK (p : Program) (r k : ℕ) : FM FForm := do
  let a := List.range k
  let zero ← constant 0
  let one ← constant 1
  let q ← fresh
  let c ← fresh
  let K ← fresh
  let B ← fresh
  let T ← fresh
  let F ← fresh
  let D ← fresh
  let R ← freshN r
  let N ← freshN r
  let S ← freshN p.length
  let φs ← packedFormulasK p r a zero one q c K B T F D R N S
  pure (.and φs)

theorem constructionK_eq (p : Program) (r k : ℕ) : constructionK p r k = construction p r k := by
  simp only [constructionK, construction, packedFormulasK_eq]

/-- The reversed node list of the kernel-friendly fast run. -/
def fastNodesRevK (p : Program) (r k : ℕ) : List NatNode :=
  match constructionK p r k (FState.init k) with
  | (φ, t) => (φ.encode t).2.rev

theorem fastNodesRevK_eq (p : Program) (r k : ℕ) : fastNodesRevK p r k = fastNodesRev p r k := by
  rw [fastNodesRevK, fastNodesRev, constructionK_eq]

end ZInQ.Compiler.NodeCheck
