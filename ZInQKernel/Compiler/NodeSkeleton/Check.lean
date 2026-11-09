import ZInQKernel.Compiler.NodeSkeleton.Core

/-!
# Chunk checks (no Mathlib)

A chunk runs one piece of the checking builder from a pinned start state. `chunkOK` checks, as
a Boolean, that the run passes all its checks, consumes all its oracle data, returns the pinned
result and ends in a state that agrees with the pinned start state of the next chunk (same
counters, tables and hot list; the pinned window is a prefix of the window), and that the hubs
of the next chunk lie beyond its start. `chunkOK_sound` unpacks it.
-/

set_option linter.constructorNameAsVariable false

namespace ZInQ.Compiler.NodeSkeleton

/-! ### Boolean equalities -/

/-- Equality of lists of numbers. -/
def natListBeq : List Nat → List Nat → Bool
  | [], [] => true
  | a :: l, b :: l' => Nat.beq a b && natListBeq l l'
  | _, _ => false

/-- Equality of lists of pairs. -/
def pairListBeq : List (Nat × Nat) → List (Nat × Nat) → Bool
  | [], [] => true
  | a :: l, b :: l' => Nat.beq a.1 b.1 && Nat.beq a.2 b.2 && pairListBeq l l'
  | _, _ => false

/-- Equality of lists of triples. -/
def tripleListBeq : List (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool
  | [], [] => true
  | a :: l, b :: l' =>
    Nat.beq a.1 b.1 && Nat.beq a.2.1 b.2.1 && Nat.beq a.2.2 b.2.2 && tripleListBeq l l'
  | _, _ => false

mutual

/-- Equality of formulas. -/
def LForm.beq : LForm → LForm → Bool
  | .eq a b, .eq a' b' => Nat.beq a a' && Nat.beq b b'
  | .atom f, .atom f' => Nat.beq f f'
  | .call j, .call j' => Nat.beq j j'
  | .and fs, .and fs' => LForm.beqList fs fs'
  | .or fs, .or fs' => LForm.beqList fs fs'
  | _, _ => false

/-- Equality of lists of formulas. -/
def LForm.beqList : List LForm → List LForm → Bool
  | [], [] => true
  | f :: fs, f' :: fs' => LForm.beq f f' && LForm.beqList fs fs'
  | _, _ => false

end

/-- `a` is a prefix of `b`. -/
def isPrefixB : List Nat → List Nat → Bool
  | [], _ => true
  | a :: l, b :: l' => Nat.beq a b && isPrefixB l l'
  | _ :: _, [] => false

/-- All lanes are empty. -/
def allEmpty : List (List Nat) → Bool
  | [] => true
  | l :: ls => l.isEmpty && allEmpty ls

/-- Every hub lies at or beyond index `n`. -/
def hubsGe (n : Nat) : List Nat → Bool
  | [] => true
  | e :: l => Nat.ble n (e / 8) && hubsGe n l

theorem natListBeq_sound : ∀ {l l' : List Nat}, natListBeq l l' = true → l = l'
  | [], [], _ => rfl
  | a :: l, b :: l', h => by
    simp only [natListBeq, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1, natListBeq_sound h.2]
  | [], _ :: _, h => by simp [natListBeq] at h
  | _ :: _, [], h => by simp [natListBeq] at h

theorem pairListBeq_sound : ∀ {l l' : List (Nat × Nat)}, pairListBeq l l' = true → l = l'
  | [], [], _ => rfl
  | a :: l, b :: l', h => by
    simp only [pairListBeq, Bool.and_eq_true, Nat.beq_eq] at h
    rw [Prod.ext h.1.1 h.1.2, pairListBeq_sound h.2]
  | [], _ :: _, h => by simp [pairListBeq] at h
  | _ :: _, [], h => by simp [pairListBeq] at h

theorem tripleListBeq_sound : ∀ {l l' : List (Nat × Nat × Nat)},
    tripleListBeq l l' = true → l = l'
  | [], [], _ => rfl
  | a :: l, b :: l', h => by
    simp only [tripleListBeq, Bool.and_eq_true, Nat.beq_eq] at h
    rw [Prod.ext h.1.1.1 (Prod.ext h.1.1.2 h.1.2), tripleListBeq_sound h.2]
  | [], _ :: _, h => by simp [tripleListBeq] at h
  | _ :: _, [], h => by simp [tripleListBeq] at h

mutual

theorem LForm.beq_sound : ∀ {f f' : LForm}, LForm.beq f f' = true → f = f'
  | .eq a b, .eq a' b', h => by
    simp only [LForm.beq, Bool.and_eq_true, Nat.beq_eq] at h; rw [h.1, h.2]
  | .atom f, .atom f', h => by simp only [LForm.beq, Nat.beq_eq] at h; rw [h]
  | .call j, .call j', h => by simp only [LForm.beq, Nat.beq_eq] at h; rw [h]
  | .and fs, .and fs', h => by
    simp only [LForm.beq] at h; rw [LForm.beqList_sound h]
  | .or fs, .or fs', h => by
    simp only [LForm.beq] at h; rw [LForm.beqList_sound h]
  | .eq _ _, .atom _, h | .eq _ _, .call _, h | .eq _ _, .and _, h | .eq _ _, .or _, h
  | .atom _, .eq _ _, h | .atom _, .call _, h | .atom _, .and _, h | .atom _, .or _, h
  | .call _, .eq _ _, h | .call _, .atom _, h | .call _, .and _, h | .call _, .or _, h
  | .and _, .eq _ _, h | .and _, .atom _, h | .and _, .call _, h | .and _, .or _, h
  | .or _, .eq _ _, h | .or _, .atom _, h | .or _, .call _, h | .or _, .and _, h => by
    simp [LForm.beq] at h

theorem LForm.beqList_sound : ∀ {l l' : List LForm}, LForm.beqList l l' = true → l = l'
  | [], [], _ => rfl
  | f :: l, f' :: l', h => by
    simp only [LForm.beqList, Bool.and_eq_true] at h
    rw [LForm.beq_sound h.1, LForm.beqList_sound h.2]
  | [], _ :: _, h => by simp [LForm.beqList] at h
  | _ :: _, [], h => by simp [LForm.beqList] at h

end

theorem isPrefixB_sound : ∀ {l l' : List Nat}, isPrefixB l l' = true → l <+: l'
  | [], l', _ => List.nil_prefix
  | a :: l, b :: l', h => by
    simp only [isPrefixB, Bool.and_eq_true, Nat.beq_eq] at h
    rw [h.1]; exact List.cons_prefix_cons.mpr ⟨rfl, isPrefixB_sound h.2⟩
  | _ :: _, [], h => by simp [isPrefixB] at h

theorem allEmpty_sound : ∀ {ls : List (List Nat)}, allEmpty ls = true → ∀ ℓ, ls.getD ℓ [] = []
  | [], _, ℓ => by simp
  | l :: ls, h, ℓ => by
    simp only [allEmpty, Bool.and_eq_true, List.isEmpty_iff] at h
    cases ℓ with
    | zero => simp [h.1]
    | succ ℓ => simpa using allEmpty_sound h.2 ℓ

theorem hubsGe_sound : ∀ {n : Nat} {l : List Nat}, hubsGe n l = true → ∀ e ∈ l, n ≤ e / 8
  | _, [], _, e, he => by simp at he
  | n, x :: l, h, e, he => by
    simp only [hubsGe, Bool.and_eq_true, Nat.ble_eq] at h
    rcases List.mem_cons.mp he with rfl | he
    · exact h.1
    · exact hubsGe_sound h.2 e he

/-! ### Chunks -/

/-- The end of a chunk: all checks passed, the oracle data consumed, and the state agrees with
the pinned start state `st` of the next chunk. -/
def endOK (h st : HState) : Bool :=
  h.ok && Nat.beq h.len st.len && Nat.beq h.next st.next && Nat.beq h.adds st.adds &&
    Nat.beq h.muls st.muls && pairListBeq h.consts st.consts && pairListBeq h.hot st.hot &&
    isPrefixB st.win h.win && h.codes.isEmpty && h.hubs.isEmpty && allEmpty h.lanes &&
    hubsGe st.len st.hubs && Nat.ble st.len st.lim && st.ok

/-- The check of a chunk with result `v`, compared by `beq`. -/
def chunkOK {α : Type} (beq : α → α → Bool) (r : α × HState) (st : HState) (v : α) : Bool :=
  beq r.1 v && endOK r.2 st

/-- What the end of a chunk guarantees. -/
structure EndRel (h st : HState) : Prop where
  ok : h.ok = true
  len : h.len = st.len
  next : h.next = st.next
  adds : h.adds = st.adds
  muls : h.muls = st.muls
  consts : h.consts = st.consts
  hot : h.hot = st.hot
  win : st.win <+: h.win
  hubs : h.hubs = []
  lanes : ∀ ℓ, h.lanes.getD ℓ [] = []
  hubsGe : ∀ e ∈ st.hubs, st.len ≤ e / 8
  lim : st.len ≤ st.lim
  stOk : st.ok = true

theorem endOK_sound {h st : HState} (hc : endOK h st = true) : EndRel h st := by
  simp only [endOK, Bool.and_eq_true, Nat.beq_eq, List.isEmpty_iff, Nat.ble_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩ := hc
  exact ⟨h1, h2, h3, h4, h5, pairListBeq_sound h6, pairListBeq_sound h7, isPrefixB_sound h8,
    h10, allEmpty_sound h11, hubsGe_sound h12, h13, h14⟩

theorem chunkOK_sound {α : Type} {beq : α → α → Bool} (hb : ∀ a b, beq a b = true → a = b)
    {r : α × HState} {st : HState} {v : α} (hc : chunkOK beq r st v = true) :
    r.1 = v ∧ EndRel r.2 st := by
  simp only [chunkOK, Bool.and_eq_true] at hc
  exact ⟨hb _ _ hc.1, endOK_sound hc.2⟩

/-! ### The prelude of the construction -/

/-- The results of the prelude: the constants `0, 1`, the variables `q, c, K, B, T, F, D` and
the blocks `R, N, S`. -/
abbrev PreludeVal : Type :=
  Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × List Nat

/-- Equality of prelude results. -/
def preludeBeq (a b : PreludeVal) : Bool :=
  Nat.beq a.1 b.1 && Nat.beq a.2.1 b.2.1 && Nat.beq a.2.2.1 b.2.2.1 &&
    Nat.beq a.2.2.2.1 b.2.2.2.1 && Nat.beq a.2.2.2.2.1 b.2.2.2.2.1 &&
    Nat.beq a.2.2.2.2.2.1 b.2.2.2.2.2.1 && Nat.beq a.2.2.2.2.2.2.1 b.2.2.2.2.2.2.1 &&
    Nat.beq a.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.1 && Nat.beq a.2.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2.1 &&
    natListBeq a.2.2.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2.2.1 &&
    natListBeq a.2.2.2.2.2.2.2.2.2.2.1 b.2.2.2.2.2.2.2.2.2.2.1 &&
    natListBeq a.2.2.2.2.2.2.2.2.2.2.2 b.2.2.2.2.2.2.2.2.2.2.2

theorem preludeBeq_sound (a b : PreludeVal) (h : preludeBeq a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := a
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := b
  simp only [preludeBeq, Bool.and_eq_true, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  rw [h1, h2, h3, h4, h5, h6, h7, h8, h9, natListBeq_sound h10, natListBeq_sound h11,
    natListBeq_sound h12]

/-- The prelude of the construction. -/
noncomputable def preludeHP (m r : Nat) : HP PreludeVal := do
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
  let S ← freshN m
  pure (zero, one, q, c, K, B, T, F, D, R, N, S)

end ZInQ.Compiler.NodeSkeleton

namespace ZInQ.Compiler.NodeSkeleton

/-- The pinned start state of the first chunk. -/
def stInit (lim : Nat) : HState := ⟨2, 2, 0, 0, [], [14, 4], [], [], [], [], lim, true⟩

/-- A pinned state with its oracle data. -/
def HState.withOracle (sc : HState) (codes hubs : List Nat) (lanes : List (List Nat)) : HState :=
  { sc with codes := codes, hubs := hubs, lanes := lanes }

/-- The values of `k` fields in base `b` of the word `x`, then `rest`. -/
def unpackWord (b : Nat) : Nat → Nat → List Nat → List Nat :=
  Nat.rec (fun _ rest => rest) (fun _ ih x rest => (x % b) :: ih (x / b) rest)

/-- Unpack a list of words of `k` fields in base `b`, keeping the first `n` fields. -/
def unpack (b k n : Nat) (ws : List Nat) : List Nat :=
  (ws.foldr (fun x acc => unpackWord b k x acc) []).take n

/-- Unpack a list of lanes. -/
def unpackLanes (b k : Nat) (ls : List (Nat × List Nat)) : List (List Nat) :=
  ls.map fun l => unpack b k l.1 l.2

end ZInQ.Compiler.NodeSkeleton

namespace ZInQ.Compiler.NodeSkeleton

/-- Equality of the results of item 5. -/
def sbBeq (a b : List LForm × List (Nat × Nat × Nat)) : Bool :=
  LForm.beqList a.1 b.1 && tripleListBeq a.2 b.2

theorem sbBeq_sound (a b : List LForm × List (Nat × Nat × Nat)) (h : sbBeq a b = true) :
    a = b := by
  simp only [sbBeq, Bool.and_eq_true] at h
  exact Prod.ext (LForm.beqList_sound h.1) (tripleListBeq_sound h.2)

theorem natListBeq_sound' (a b : List Nat) (h : natListBeq a b = true) : a = b :=
  natListBeq_sound h

theorem formsBeq_sound (a b : List LForm) (h : LForm.beqList a b = true) : a = b :=
  LForm.beqList_sound h

theorem natBeq_sound (a b : Nat) (h : Nat.beq a b = true) : a = b := Nat.eq_of_beq_eq_true h

end ZInQ.Compiler.NodeSkeleton
