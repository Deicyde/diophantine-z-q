import ZInQKernel.Compiler.NodeCheck.Fast
import ZInQKernel.Compiler.NodeSkeleton.Core

/-!
# The checking builder simulates the fast builder: the relation and the primitives

`Rel Hall Hf Ff t h` relates a state `t` of the fast builder `NodeCheck.FM` (with its
hash-consing table) to a state `h` of the checking builder `HP`. Besides the shared counters,
it says that the table of `t` answers like `List.idxOf?` on its node list `P`, that the
tabled nodes of `P` are distinct and every child is older than its parent, that the window of
`h` is a prefix of the records of `P`, that the hot list and the constant table of `h` are
correct, and the bookkeeping of hubs and lanes: `Hall` is the global hub list, `Hf` the hubs
of the later chunks and `Ff ℓ` the entries of lane `ℓ` in the later chunks. The key fact
(`hist`) is that the entry of every node of a hub group is no longer in the lanes.

`Sim2 er m m'` says that the fast construction `m` and the checking construction `m'`, run
from related states, end in related states with results related by `er`, as soon as the
checking run ends with `ok = true`.
-/

namespace ZInQ.Compiler.NodeSkeleton

open Natural NodeCheck Universal

/-! ### Conversions -/

/-- Instructions. -/
def toLI : RM.Instr → LInstr
  | .inc j x => .inc j x
  | .dec j x y => .dec j x y
  | .halt => .halt

mutual

/-- Formulas. -/
def toL : FForm → LForm
  | .eq a b => .eq a b
  | .atom f => .atom f
  | .call j => .call j
  | .and fs => .and (toLs fs)
  | .or fs => .or (toLs fs)

/-- Lists of formulas. -/
def toLs : List FForm → List LForm
  | [] => []
  | f :: fs => toL f :: toLs fs

end

theorem toLs_eq (fs : List FForm) : toLs fs = fs.map toL := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [toLs, ih]

theorem lpairB_eq : lpairB = pairB := rfl

theorem lintKey_eq : lintKey = intKey := by
  funext c; cases c <;> rfl

theorem opKey_add (a b : ℕ) : opKey 0 a b = nodeKey (.add a b) := by
  simp [opKey, nodeKey, lpairB_eq]

theorem opKey_mul (a b : ℕ) : opKey 1 a b = nodeKey (.mul a b) := by
  simp [opKey, nodeKey, lpairB_eq]

/-! ### Nodes -/

/-- Addition and multiplication nodes. -/
def isOp : NatNode → Bool
  | .add _ _ => true
  | .mul _ _ => true
  | _ => false

/-- The youngest child of an addition or multiplication node. -/
def youngest : NatNode → ℕ
  | .add a b => max a b
  | .mul a b => max a b
  | _ => 0

theorem tabled_of_isOp {n : NatNode} (h : isOp n = true) : tabled n = true := by
  cases n <;> simp_all [isOp, tabled]

/-! ### Records -/

/-- The hub flag of the node of index `j`. -/
def flagOf (Hall : List ℕ) (j : ℕ) : Bool := decide (j ∈ Hall.map (· / 8))

/-- The records of a reversed node list, newest first. -/
def recsOf (Hall : List ℕ) : List NatNode → List ℕ
  | [] => []
  | n :: rev => (2 * nodeKey n + cond (flagOf Hall rev.length) 1 0) :: recsOf Hall rev

theorem getElem?_recsOf (Hall : List ℕ) (rev : List NatNode) (i : ℕ) :
    (recsOf Hall rev)[i]? =
      rev[i]?.map fun n => 2 * nodeKey n + cond (flagOf Hall (rev.length - 1 - i)) 1 0 := by
  induction rev generalizing i with
  | nil => rfl
  | cons n rev ih =>
    cases i with
    | zero => simp [recsOf]
    | succ i =>
      simp only [recsOf, List.getElem?_cons_succ, ih, List.length_cons]
      rw [show rev.length + 1 - 1 - (i + 1) = rev.length - 1 - i by omega]

/-! ### The relation -/

/-- The node list of a fast state, in order. -/
abbrev nodesOf (t : FState) : List NatNode := t.rev.reverse

/-- The remaining entries of lane `ℓ`. -/
def remL (Ff : ℕ → List ℕ) (h : HState) (ℓ : ℕ) : List ℕ := h.lanes.getD ℓ [] ++ Ff ℓ

/-- Strictly increasing hub indices. -/
def HubSorted (Hall : List ℕ) : Prop := Hall.Pairwise fun a b => a / 8 < b / 8

/-- Related states. -/
structure Rel (Hall Hf : List ℕ) (Ff : ℕ → List ℕ) (t : FState) (h : HState) : Prop where
  len : h.len = t.len
  next : h.next = t.next
  lenRev : t.len = t.rev.length
  table : ∀ n, tabled n = true → t.table.find n = (nodesOf t).idxOf? n
  nodup : ∀ (i j : ℕ) (n : NatNode), (nodesOf t)[i]? = some n → (nodesOf t)[j]? = some n → tabled n = true →
    i = j
  child : ∀ (j : ℕ) (n : NatNode), (nodesOf t)[j]? = some n → isOp n = true → youngest n < j
  adds : h.adds = countKind .add t.rev
  muls : h.muls = countKind .mul t.rev
  consts : ∀ c, constFind (lintKey c) h.consts = (nodesOf t).idxOf? (.const c)
  hot : ∀ e ∈ h.hot, ∃ n, (nodesOf t)[e.2]? = some n ∧ isOp n = true ∧ nodeKey n = e.1
  win : h.win <+: recsOf Hall t.rev
  lim : h.len ≤ h.lim
  hubs : h.hubs ++ Hf = Hall.filter fun e => h.len ≤ e / 8
  hubsLim : ∀ e ∈ Hf, h.lim ≤ e / 8
  laneNodup : ∀ ℓ, (remL Ff h ℓ).Nodup
  laneLabel : ∀ ℓ, ∀ e ∈ remL Ff h ℓ, ℓ < 8 ∧ 8 * (e / laneBase) + ℓ ∈ Hall
  hist : ∀ (j : ℕ) (n : NatNode), (nodesOf t)[j]? = some n → isOp n = true → flagOf Hall (youngest n) = true →
    ∀ ℓ, youngest n * laneBase + nodeKey n ∉ remL Ff h ℓ
  sorted : HubSorted Hall

/-! ### The loops -/

section Loops

variable {Hall : List ℕ}

theorem hubSorted_eq {Hall : List ℕ} (hs : HubSorted Hall) {a b : ℕ} (ha : a ∈ Hall)
    (hb : b ∈ Hall) (hab : a / 8 = b / 8) : a = b := by
  induction Hall with
  | nil => simp at ha
  | cons x l ih =>
    rw [HubSorted, List.pairwise_cons] at hs
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; have := hs.1 b hb'; omega
    · subst hb'; have := hs.1 a ha'; omega
    · exact ih hs.2 ha' hb'

/-- `Nat.beq` of distinct numbers. -/
theorem nbeq_false {a b : ℕ} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem filter_ge_cons_head {l : List ℕ} (hs : HubSorted l) {len e : ℕ} {rest : List ℕ}
    (h : l.filter (fun e => len ≤ e / 8) = e :: rest) :
    len ≤ e / 8 ∧ (∀ x ∈ rest, e / 8 < x / 8) ∧ (∀ x ∈ l, x / 8 < e / 8 → x / 8 < len) := by
  induction l with
  | nil => simp at h
  | cons x l ih =>
    rw [HubSorted, List.pairwise_cons] at hs
    by_cases hx : len ≤ x / 8
    · rw [List.filter_cons_of_pos (by simpa using hx)] at h
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      refine ⟨hx, fun y hy => hs.1 y (List.mem_of_mem_filter hy), fun y hy hlt => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · have := hs.1 y hy; omega
    · rw [List.filter_cons_of_neg (by simpa using hx)] at h
      obtain ⟨h1, h2, h3⟩ := ih hs.2 h
      refine ⟨h1, h2, fun y hy hlt => ?_⟩
      rcases List.mem_cons.mp hy with rfl | hy
      · omega
      · exact h3 y hy hlt

theorem filter_ge_succ {l : List ℕ} {len : ℕ} (hn : ∀ x ∈ l, x / 8 ≠ len) :
    l.filter (fun e => len + 1 ≤ e / 8) = l.filter (fun e => len ≤ e / 8) := by
  apply List.filter_congr
  intro x hx
  have := hn x hx
  simp only [decide_eq_decide]
  omega

/-- The hub step: the flag of the new node and the remaining hubs. -/
theorem hubStep_spec {Hall Hf hubs : List ℕ} (hs : HubSorted Hall) {len lim : ℕ}
    (hh : hubs ++ Hf = Hall.filter fun e => len ≤ e / 8) (hl : ∀ e ∈ Hf, lim ≤ e / 8)
    (hlen : len < lim) :
    (hubStep len hubs).1 = flagOf Hall len ∧
      (hubStep len hubs).2 ++ Hf = Hall.filter fun e => len + 1 ≤ e / 8 := by
  cases hubs with
  | nil =>
    simp only [List.nil_append] at hh
    have hn : ∀ x ∈ Hall, x / 8 ≠ len := by
      intro x hx hxe
      have : x ∈ Hf := by rw [hh]; exact List.mem_filter.mpr ⟨hx, by simp; omega⟩
      have := hl x this; omega
    refine ⟨?_, ?_⟩
    · show false = flagOf Hall len
      unfold flagOf
      rw [eq_comm, decide_eq_false_iff_not]
      simp only [List.mem_map, not_exists, not_and]
      exact hn
    · show [] ++ Hf = _
      rw [List.nil_append, hh, filter_ge_succ hn]
  | cons e hs' =>
    have hf := filter_ge_cons_head hs hh.symm
    obtain ⟨h1, h2, h3⟩ := hf
    have he : e ∈ Hall := by
      have : e ∈ e :: hs' ++ Hf := by simp
      rw [hh] at this; exact List.mem_of_mem_filter this
    by_cases heq : e / 8 = len
    · have hb : Nat.beq (e / 8) len = true := by simpa using heq
      have e1 : hubStep len (e :: hs') = (true, hs') := by
        show (bif Nat.beq (e / 8) len then (true, hs') else (false, e :: hs')) = _
        rw [hb]; rfl
      rw [e1]
      refine ⟨?_, ?_⟩
      · simp only [flagOf]
        exact (decide_eq_true (List.mem_map.mpr ⟨e, he, heq⟩)).symm
      · have : Hall.filter (fun e => len + 1 ≤ e / 8) =
            (Hall.filter fun e => len ≤ e / 8).filter (fun e => len + 1 ≤ e / 8) := by
          rw [List.filter_filter]
          apply List.filter_congr
          intro x _
          by_cases h1 : len + 1 ≤ x / 8 <;> by_cases h2 : len ≤ x / 8 <;> simp [h1, h2] <;> omega
        rw [this, ← hh, List.cons_append, List.filter_cons_of_neg (by simp; omega)]
        symm
        apply List.filter_eq_self.mpr
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · have := h2 x (List.mem_append_left _ hx); simp; omega
        · have := hl x hx; simp; omega
    · have hb : Nat.beq (e / 8) len = false := nbeq_false heq
      have e1 : hubStep len (e :: hs') = (false, e :: hs') := by
        show (bif Nat.beq (e / 8) len then (true, hs') else (false, e :: hs')) = _
        rw [hb]; rfl
      rw [e1]
      have hn : ∀ x ∈ Hall, x / 8 ≠ len := by
        intro x hx hxe
        by_cases hlt : x / 8 < e / 8
        · have := h3 x hx hlt; omega
        · have : x ∈ e :: hs' ++ Hf := by
            rw [hh]; exact List.mem_filter.mpr ⟨hx, by simp; omega⟩
          rcases List.mem_append.mp this with hx' | hx'
          · rcases List.mem_cons.mp hx' with rfl | hx'
            · exact heq hxe
            · have := h2 x (List.mem_append_left _ hx'); omega
          · have := hl x hx'; omega
      refine ⟨?_, ?_⟩
      · simp only [flagOf]
        symm
        simp only [decide_eq_false_iff_not, List.mem_map, not_exists, not_and]
        exact hn
      · rw [hh, filter_ge_succ hn]

theorem scan_zero (k : ℕ) (win : List ℕ) :
    scan k 0 win = List.casesOn (motive := fun _ => Bool) win false
      (fun r _ => Nat.beq (r % 2) 0) := rfl

theorem scan_succ (k d : ℕ) (win : List ℕ) :
    scan k (d + 1) win = List.casesOn (motive := fun _ => Bool) win false
      (fun r w' => bif Nat.beq (r / 2) k then false else scan k d w') := rfl

theorem rec_div (k : ℕ) (b : Bool) : (2 * k + cond b 1 0) / 2 = k := by
  cases b <;> simp only [cond] <;> omega

theorem rec_mod (k : ℕ) (b : Bool) : (2 * k + cond b 1 0) % 2 = cond b 1 0 := by
  cases b <;> simp only [cond] <;> omega

/-- The scan: the `d` newest nodes have keys other than `k`, and the next one is not a
hub. -/
theorem scan_spec {k d : ℕ} {win : List ℕ} {rev : List NatNode} (hw : win <+: recsOf Hall rev)
    (hs : scan k d win = true) :
    d < rev.length ∧ (∀ i < d, ∀ n, rev[i]? = some n → nodeKey n ≠ k) ∧
      flagOf Hall (rev.length - 1 - d) = false := by
  induction d generalizing win rev with
  | zero =>
    rw [scan_zero] at hs
    cases win with
    | nil => exact absurd hs (by simp)
    | cons r w =>
      cases rev with
      | nil => simp [recsOf] at hw
      | cons n rev =>
        simp only [recsOf, List.cons_prefix_cons] at hw
        obtain ⟨rfl, -⟩ := hw
        simp only [Nat.beq_eq] at hs
        rw [rec_mod] at hs
        refine ⟨by simp, fun i hi => absurd hi (by omega), ?_⟩
        simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_zero]
        cases hf : flagOf Hall rev.length <;> simp_all
  | succ d ih =>
    rw [scan_succ] at hs
    cases win with
    | nil => exact absurd hs (by simp)
    | cons r w =>
      cases rev with
      | nil => simp [recsOf] at hw
      | cons n rev =>
        simp only [recsOf, List.cons_prefix_cons] at hw
        obtain ⟨rfl, hw⟩ := hw
        simp only at hs
        rw [rec_div] at hs
        cases hb : Nat.beq (nodeKey n) k
        · rw [hb] at hs
          obtain ⟨h1, h2, h3⟩ := ih hw hs
          refine ⟨by simp; omega, fun i hi m hm => ?_, ?_⟩
          · cases i with
            | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
              subst hm
              exact Nat.ne_of_beq_eq_false hb
            | succ i => exact h2 i (by omega) m (by simpa using hm)
          · simp only [List.length_cons]
            rw [show rev.length + 1 - 1 - (d + 1) = rev.length - 1 - d by omega]
            exact h3
        · rw [hb] at hs; exact absurd hs (by simp)

theorem constFind_cons (ik ik' j : ℕ) (cs : List (ℕ × ℕ)) :
    constFind ik' ((ik, j) :: cs) = if ik = ik' then some j else constFind ik' cs := by
  show (bif Nat.beq ik ik' then some j else constFind ik' cs) = _
  by_cases h : ik = ik'
  · subst h; simp
  · have : Nat.beq ik ik' = false := nbeq_false h
    rw [this]; simp [h]

theorem hotTake_spec {k j : ℕ} {hot rest : List (ℕ × ℕ)} (h : hotTake k hot = some (j, rest)) :
    (k, j) ∈ hot ∧ ∀ e ∈ rest, e ∈ hot := by
  induction hot generalizing rest with
  | nil => exact absurd h (by simp [hotTake])
  | cons e hot ih =>
    have e1 : hotTake k (e :: hot) = bif Nat.beq e.1 k then some (e.2, hot) else
      Option.casesOn (motive := fun _ => Option (ℕ × List (ℕ × ℕ))) (hotTake k hot) none
        (fun p => some (p.1, e :: p.2)) := rfl
    rw [e1] at h
    cases hb : Nat.beq e.1 k
    · rw [hb] at h
      cases hr : hotTake k hot with
      | none => rw [hr] at h; exact absurd h (by simp)
      | some p =>
        rw [hr] at h
        simp only [Bool.cond_false, Option.some.injEq] at h
        obtain ⟨p1, p2⟩ := p
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := ih hr
        refine ⟨List.mem_cons_of_mem _ h1, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (h2 x hx)
    · rw [hb] at h
      simp only [Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have : e.1 = k := by simpa using hb
      refine ⟨?_, fun x hx => List.mem_cons_of_mem _ hx⟩
      rw [← this]; exact List.mem_cons_self

theorem lanePop_spec {ℓ e : ℕ} {lanes lanes' : List (List ℕ)}
    (h : lanePop ℓ e lanes = (true, lanes')) :
    lanes.getD ℓ [] = e :: lanes'.getD ℓ [] ∧ ∀ ℓ', ℓ' ≠ ℓ → lanes'.getD ℓ' [] = lanes.getD ℓ' [] := by
  induction ℓ generalizing lanes lanes' with
  | zero =>
    cases lanes with
    | nil => exact absurd h (by simp [lanePop])
    | cons l ls =>
      cases l with
      | nil => exact absurd h (by simp [lanePop])
      | cons x l' =>
        have e1 : lanePop 0 e ((x :: l') :: ls) =
            bif Nat.beq x e then (true, l' :: ls) else (false, (x :: l') :: ls) := rfl
        rw [e1] at h
        cases hb : Nat.beq x e
        · rw [hb] at h; exact absurd h (by simp)
        · rw [hb] at h
          simp only [Bool.cond_true, Prod.mk.injEq, true_and] at h
          subst h
          have : x = e := by simpa using hb
          subst this
          refine ⟨rfl, fun ℓ' hℓ' => ?_⟩
          cases ℓ' with
          | zero => exact absurd rfl hℓ'
          | succ ℓ' => rfl
  | succ ℓ ih =>
    cases lanes with
    | nil => exact absurd h (by simp [lanePop])
    | cons l ls =>
      have e1 : lanePop (ℓ + 1) e (l :: ls) =
          match lanePop ℓ e ls with
          | (b, ls'') => (b, l :: ls'') := rfl
      rw [e1] at h
      cases hr : lanePop ℓ e ls with
      | mk b ls'' =>
        rw [hr] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := ih hr
        refine ⟨by simpa using h1, fun ℓ' hℓ' => ?_⟩
        cases ℓ' with
        | zero => rfl
        | succ ℓ' => simpa using h2 ℓ' (by omega)

end Loops

end ZInQ.Compiler.NodeSkeleton
