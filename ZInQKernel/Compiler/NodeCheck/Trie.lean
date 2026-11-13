import ZInQKernel.Compiler.Circuits.Counts

/-!
# Binary tries keyed by natural numbers, and numeric keys of nodes

A trie `NTrie α` stores values at natural keys: the key `0` lives at the root, and a key
`k > 0` lives in the left subtree under the key `k / 2` if `k` is even and in the right
subtree otherwise. Lookup (`NTrie.find`) is structural recursion on the trie; insertion
(`NTrie.ins`) is structural recursion on a fuel argument, and any fuel above the key suffices
(`find_ins`). The tests are Boolean tests on `Nat` primitives, which the kernel evaluates on
literals.

`nodeKey` is a numeric key of nodes, injective on the nodes other than call nodes
(`key_inj`). The fast builder of the node check uses a trie from keys to node indices as its
hash-consing table.
-/

namespace ZInQ.Compiler.NodeCheck

open Natural

/-- Binary tries with values in `α` at natural keys. -/
inductive NTrie (α : Type) where
  | leaf
  | node (v : Option α) (l r : NTrie α)

namespace NTrie

variable {α : Type}

/-- The value stored at key `k` (structural recursion; the compiled implementation of
`find`). -/
def findS : NTrie α → ℕ → Option α
  | leaf, _ => none
  | node v l r, k =>
    cond (Nat.beq k 0) v
      (cond (Nat.beq (Nat.mod k 2) 0) (findS l (Nat.div k 2)) (findS r (Nat.div k 2)))

/-- The value stored at key `k`. It is written with the recursor and `Nat` primitives, which
the kernel reduces about twice as fast as the structural definition `findS`. -/
noncomputable def find (t : NTrie α) : ℕ → Option α :=
  NTrie.rec (motive := fun _ => ℕ → Option α) (fun _ => none)
    (fun v _ _ fl fr k =>
      cond (Nat.beq k 0) v (cond (Nat.beq (Nat.mod k 2) 0) (fl (Nat.div k 2)) (fr (Nat.div k 2))))
    t

@[csimp] theorem find_eq_findS : @find = @findS := by
  funext α t
  induction t with
  | leaf => rfl
  | node v l r ihl ihr =>
    funext k
    simp only [find, findS] at *
    rw [← ihl, ← ihr]

/-- The root value and the two subtrees (a leaf has no value and two leaf subtrees). -/
def view : NTrie α → Option α × NTrie α × NTrie α
  | leaf => (none, leaf, leaf)
  | node v l r => (v, l, r)

/-- One step of insertion: store `a` at key `k` in `t`, inserting into a subtree with `g`. -/
def insStep (g : NTrie α → ℕ → α → NTrie α) (t : NTrie α) (k : ℕ) (a : α) : NTrie α :=
  NTrie.casesOn (motive := fun _ => NTrie α) t
    (cond (Nat.beq k 0) (node (some a) leaf leaf)
      (cond (Nat.beq (Nat.mod k 2) 0) (node none (g leaf (Nat.div k 2) a) leaf)
        (node none leaf (g leaf (Nat.div k 2) a))))
    (fun v l r => cond (Nat.beq k 0) (node (some a) l r)
      (cond (Nat.beq (Nat.mod k 2) 0) (node v (g l (Nat.div k 2) a) r)
        (node v l (g r (Nat.div k 2) a))))

/-- Store `a` at key `k`, with fuel `f` (structural recursion; the compiled implementation
of `ins`). -/
def insS : ℕ → NTrie α → ℕ → α → NTrie α
  | 0, t, _, _ => t
  | f + 1, t, k, a => insStep (insS f) t k a

/-- Store `a` at key `k`, with fuel `f` (any `f > k` suffices), written with the recursor. -/
noncomputable def ins (f : ℕ) : NTrie α → ℕ → α → NTrie α :=
  Nat.rec (motive := fun _ => NTrie α → ℕ → α → NTrie α) (fun t _ _ => t)
    (fun _ g t k a => insStep g t k a) f

@[csimp] theorem ins_eq_insS : @ins = @insS := by
  funext α f
  induction f with
  | zero => rfl
  | succ f ih =>
    funext t k a
    simp only [ins, insS] at *
    rw [← ih]

theorem find_node (v : Option α) (l r : NTrie α) (k : ℕ) :
    (node v l r).find k = if k = 0 then v else if k % 2 = 0 then l.find (k / 2)
      else r.find (k / 2) := by
  show cond (Nat.beq k 0) v (cond (Nat.beq (Nat.mod k 2) 0) (l.find (Nat.div k 2))
    (r.find (Nat.div k 2))) = _
  simp only [cond_eq_ite, Nat.beq_eq]
  rfl

theorem find_view (t : NTrie α) (k : ℕ) :
    t.find k = (node t.view.1 t.view.2.1 t.view.2.2).find k := by
  cases t with
  | leaf => rw [find_node]; simp only [view, ite_self]; split <;> rfl
  | node v l r => rfl

theorem ins_succ (f : ℕ) (t : NTrie α) (k : ℕ) (a : α) :
    t.ins (f + 1) k a =
      if k = 0 then node (some a) t.view.2.1 t.view.2.2
      else if k % 2 = 0 then node t.view.1 (t.view.2.1.ins f (k / 2) a) t.view.2.2
      else node t.view.1 t.view.2.1 (t.view.2.2.ins f (k / 2) a) := by
  cases t <;> simp only [ins, insStep, cond_eq_ite, Nat.beq_eq, view] <;> rfl

theorem find_ins (f : ℕ) (t : NTrie α) (k : ℕ) (a : α) (hk : k < f) (k' : ℕ) :
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

@[simp] theorem find_leaf (k : ℕ) : (leaf : NTrie α).find k = none := rfl

/-- Store `a` at key `k` (fuel `k + 1`). -/
def insert (t : NTrie α) (k : ℕ) (a : α) : NTrie α := t.ins (k + 1) k a

theorem find_insert (t : NTrie α) (k : ℕ) (a : α) (k' : ℕ) :
    (t.insert k a).find k' = if k' = k then some a else t.find k' :=
  find_ins _ t k a (Nat.lt_succ_self k) k'

end NTrie

/-! ### Numeric keys of nodes -/

/-- The Cantor-style pairing `Nat.pair`, with a Boolean test. -/
def pairB (a b : ℕ) : ℕ := bif a.blt b then b * b + a else a * a + a + b

theorem pairB_eq (a b : ℕ) : pairB a b = Nat.pair a b := by
  simp only [pairB, Nat.pair, cond_eq_ite, Nat.blt_eq]

/-- An injective code of the integers. -/
def intKey : ℤ → ℕ
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

theorem intKey_inj {a b : ℤ} (h : intKey a = intKey b) : a = b := by
  cases a <;> cases b <;> simp only [intKey] at h <;> first | omega | (congr 1; omega)

/-- The numeric key of a node (`0` for call nodes, which are never looked up). -/
def nodeKey : NatNode → ℕ
  | .const c => 5 * intKey c + 1
  | .var i => 5 * i + 2
  | .add j k => 5 * pairB j k + 3
  | .mul j k => 5 * pairB j k + 4
  | .call _ _ _ _ => 0

/-- Keys are injective on nodes other than call nodes. -/
theorem key_inj {n n' : NatNode} (hn : n.isCall = false) (hn' : n'.isCall = false)
    (h : nodeKey n = nodeKey n') : n = n' := by
  cases n <;> cases n' <;>
    simp only [nodeKey, NatNode.isCall, pairB_eq, NatNode.const.injEq, NatNode.var.injEq,
      NatNode.add.injEq, NatNode.mul.injEq, Bool.true_eq_false] at h hn hn' ⊢ <;> (try omega)
  all_goals first | exact intKey_inj (by omega) | exact Nat.pair_eq_pair.mp (by omega)

/-! ### The hash-consing table -/

/-- The nodes kept in the hash-consing table: constants, additions and multiplications
(variable nodes are always fresh and call nodes are never looked up). -/
def tabled : NatNode → Bool
  | .const _ => true
  | .add _ _ => true
  | .mul _ _ => true
  | _ => false

theorem isCall_of_tabled {n : NatNode} (h : tabled n = true) : n.isCall = false := by
  cases n <;> simp_all [tabled, NatNode.isCall]

/-- The hash-consing table: node indices at the keys of tabled nodes. -/
abbrev Table : Type := NTrie ℕ

/-- The empty table. -/
def Table.empty : Table := NTrie.leaf

/-- The index stored for a node. -/
def Table.find (t : Table) (n : NatNode) : Option ℕ := NTrie.find t (nodeKey n)

/-- Store the index `j` for the node `n`. -/
def Table.insert (t : Table) (n : NatNode) (j : ℕ) : Table := NTrie.insert t (nodeKey n) j

@[simp] theorem Table.find_empty (n : NatNode) : Table.empty.find n = none := rfl

theorem Table.find_insert (t : Table) {n : NatNode} (hn : tabled n = true) (j : ℕ) {m : NatNode}
    (hm : tabled m = true) : (t.insert n j).find m = if m = n then some j else t.find m := by
  unfold Table.find Table.insert
  rw [NTrie.find_insert]
  congr 1
  apply propext
  constructor
  · exact key_inj (isCall_of_tabled hm) (isCall_of_tabled hn)
  · rintro rfl; rfl

end ZInQ.Compiler.NodeCheck
