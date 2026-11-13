/-!
# The checking builder (no Mathlib)

A transcription of the fast builder of `ZInQKernel/Compiler/NodeCheck/` (`FM`, its macros and
the kernel-friendly packed construction `constructionK`) into a monad `HP` whose state keeps no
hash-consing table. This module imports nothing beyond `Init`, so that the kernel runs of the
builder start from a small memory baseline.

The answers of the table are replaced by pinned oracle data, checked as the run goes:

* every addition or multiplication call reads a code: a hit (the node is found in the *hot
  list* of pairs `(key, index)`, which only ever holds nodes that exist), a *local miss* (the
  node is new: the run compares its key with the records of the nodes created after its
  youngest child, and checks that the youngest child is not a hub), or a *far miss* in lane `ℓ`
  (the node is new: it must be the head of the pinned lane `ℓ`, whose entries are checked
  globally by `Static.lean`);
* constants are looked up in a complete table of the constants created so far;
* every created node pushes a *record* `2 · key + flag` onto the window `win` (newest first);
  the flag says whether the node is a *hub*, read from the pinned hub list (sorted by index).

A failed check clears the flag `ok`; the run goes on with garbage values. The soundness of the
checks is proved in `Sim.lean`.
-/

set_option linter.constructorNameAsVariable false

namespace ZInQ.Compiler.NodeSkeleton

noncomputable section

/-! ### Data types -/

/-- Formulas: node indices only (a copy of `NodeCheck.FForm`). -/
inductive LForm
  | eq (a b : Nat)
  | atom (f : Nat)
  | call (j : Nat)
  | and (fs : List LForm)
  | or (fs : List LForm)

/-- Register-machine instructions (a copy of `RM.Instr`). -/
inductive LInstr
  | inc (j x : Nat)
  | dec (j x y : Nat)
  | halt

/-- The state of the checking builder. -/
structure HState where
  /-- The length of the node list. -/
  len : Nat
  /-- The variable counter. -/
  next : Nat
  /-- The number of addition nodes. -/
  adds : Nat
  /-- The number of multiplication nodes. -/
  muls : Nat
  /-- The constants created so far: `(intKey c, index)`. -/
  consts : List (Nat × Nat)
  /-- The records `2 · key + flag` of the last nodes, newest first. -/
  win : List Nat
  /-- The hot list: pairs `(key, index)` of existing nodes. -/
  hot : List (Nat × Nat)
  /-- The codes of the remaining addition and multiplication calls. -/
  codes : List Nat
  /-- The remaining hubs `8 · index + label`, by increasing index. -/
  hubs : List Nat
  /-- The remaining entries `y · 2^42 + key` of the far lanes. -/
  lanes : List (List Nat)
  /-- A bound on the length (the end of the current chunk). -/
  lim : Nat
  /-- All checks passed so far. -/
  ok : Bool

/-- Checking constructions. -/
def HP (α : Type) : Type := HState → α × HState

namespace HP

instance : Monad HP where
  pure a s := (a, s)
  bind m f s := match m s with
    | (a, s') => f a s'

end HP

/-! ### Keys -/

/-- The Cantor-style pairing with a Boolean test (a copy of `NodeCheck.pairB`). -/
def lpairB (a b : Nat) : Nat := bif a.blt b then b * b + a else a * a + a + b

/-- An injective code of the integers (a copy of `NodeCheck.intKey`). -/
def lintKey : Int → Nat
  | .ofNat n => 2 * n
  | .negSucc n => 2 * n + 1

/-- The key of an addition (`op = 0`) or multiplication (`op = 1`) node. -/
def opKey (op a b : Nat) : Nat := 5 * lpairB a b + 3 + op

/-- The base of the far-lane entries. -/
def laneBase : Nat := 4398046511104

/-! ### Small loops (written with recursors, which the kernel reduces quickly) -/

/-- `k n`, after the kernel has evaluated `n`. -/
def force {α : Type} (n : Nat) (k : Nat → α) : α := bif Nat.beq n 0 then k n else k n

/-- The hub flag of a new node of index `len` and the remaining hubs. -/
def hubStep (len : Nat) (hubs : List Nat) : Bool × List Nat :=
  List.casesOn (motive := fun _ => Bool × List Nat) hubs (false, [])
    (fun h hs => bif Nat.beq (h / 8) len then (true, hs) else (false, h :: hs))

/-- No record among the first `d` has key `k`, and the next record has flag `0`. -/
def scan (k : Nat) (d : Nat) (win : List Nat) : Bool :=
  Nat.rec (motive := fun _ => List Nat → Bool)
    (fun w => List.casesOn (motive := fun _ => Bool) w false (fun r _ => Nat.beq (r % 2) 0))
    (fun _ ih w => List.casesOn (motive := fun _ => Bool) w false
      (fun r w' => bif Nat.beq (r / 2) k then false else ih w')) d win

/-- Remove the entry of key `k` from the hot list: its index and the other entries. -/
def hotTake (k : Nat) (hot : List (Nat × Nat)) : Option (Nat × List (Nat × Nat)) :=
  List.rec (motive := fun _ => Option (Nat × List (Nat × Nat))) none
    (fun e rest ih => bif Nat.beq e.1 k then some (e.2, rest) else
      Option.casesOn (motive := fun _ => Option (Nat × List (Nat × Nat))) ih none
        (fun p => some (p.1, e :: p.2))) hot

/-- The index of the constant of key `ik`. -/
def constFind (ik : Nat) (cs : List (Nat × Nat)) : Option Nat :=
  List.rec (motive := fun _ => Option Nat) none
    (fun e _ ih => bif Nat.beq e.1 ik then some e.2 else ih) cs

/-- Pop the entry `e` from the head of lane `ℓ`: success and the new lanes. -/
def lanePop (ℓ : Nat) (e : Nat) (lanes : List (List Nat)) : Bool × List (List Nat) :=
  Nat.rec (motive := fun _ => List (List Nat) → Bool × List (List Nat))
    (fun ls => List.casesOn (motive := fun _ => Bool × List (List Nat)) ls (false, [])
      (fun l ls' => List.casesOn (motive := fun _ => Bool × List (List Nat)) l (false, [] :: ls')
        (fun x l' => bif Nat.beq x e then (true, l' :: ls') else (false, (x :: l') :: ls'))))
    (fun _ ih ls => List.casesOn (motive := fun _ => Bool × List (List Nat)) ls (false, [])
      (fun l ls' => match ih ls' with
        | (b, ls'') => (b, l :: ls''))) ℓ lanes

/-! ### Primitives -/

/-- A failed check. -/
def HState.fail (h : HState) : HState := { h with ok := false }

/-- Create a node of key `k` after the check `c`, with the new counter `nx`, node counts,
constant table, hot list, codes and lanes. Also checks `len < lim`. -/
def create (k : Nat) (c : Bool) (nx adds muls : Nat) (consts hot : List (Nat × Nat))
    (codes : List Nat) (lanes : List (List Nat)) (h : HState) : HState :=
  force h.len fun len =>
  match hubStep len h.hubs with
  | (f, hubs') =>
    let mk := fun o : Bool => (⟨len + 1, nx, adds, muls, consts, (2 * k + cond f 1 0) :: h.win,
      hot, codes, hubs', lanes, h.lim, o⟩ : HState)
    cond (h.ok && c && len.blt h.lim) (mk true) (mk false)

/-- A fresh variable `X_c`. -/
def fresh : HP Nat := fun h =>
  (h.len, force h.next fun nx =>
    create (5 * nx + 2) true (nx + 1) h.adds h.muls h.consts h.hot h.codes h.lanes h)

/-- The constant `c`. -/
def constant (c : Int) : HP Nat := fun h =>
  match constFind (lintKey c) h.consts with
  | some j => (j, h)
  | none =>
    (h.len, create (5 * lintKey c + 1) true h.next h.adds h.muls ((lintKey c, h.len) :: h.consts)
      h.hot h.codes h.lanes h)

/-- The call of the power template on a fresh block of `79` variables. -/
def callPower (_ _ _ : Nat) : HP LForm := fun h =>
  (.call h.len, force h.next fun nx =>
    create 0 true (nx + 79) h.adds h.muls h.consts h.hot h.codes h.lanes h)

/-- Create the addition (`op = 0`) or multiplication (`op = 1`) node of key `k`, after the
check `c`; `hotIns` says whether it enters the hot list. -/
def createOp (op k : Nat) (c hotIns : Bool) (codes : List Nat) (lanes : List (List Nat))
    (h : HState) : HState :=
  force h.adds fun adds => force h.muls fun muls =>
  create k c h.next (bif Nat.beq op 0 then adds + 1 else adds)
    (bif Nat.beq op 0 then muls else muls + 1) h.consts
    (bif hotIns then (k, h.len) :: h.hot else h.hot) codes lanes h

/-- The addition (`op = 0`) or multiplication (`op = 1`) node of `a` and `b`. -/
def nodeOp (op a b : Nat) : HP Nat := fun h =>
  match h.codes with
  | [] => (0, h.fail)
  | c :: cs =>
    let k := opKey op a b
    let kind := c % 8
    bif Nat.beq kind 1 then
      match hotTake k h.hot with
      | none => (0, { h with codes := cs, ok := false })
      | some (j, rest) =>
        (j, { h with codes := cs, hot := bif Nat.beq (c / 8) 0 then (k, j) :: rest else rest })
    else
      let y := bif a.blt b then b else a
      bif Nat.beq kind 0 then
        (h.len, createOp op k (y.blt h.len && scan k (h.len - 1 - y) h.win)
          (Nat.beq (c / 8) 1) cs h.lanes h)
      else
        match lanePop (kind - 2) (y * laneBase + k) h.lanes with
        | (b, lanes') =>
          (h.len, createOp op k (y.blt h.len && k.blt laneBase && b) (Nat.beq (c / 8) 1) cs
            lanes' h)

/-! ### Formulas and gadgets (transcribed from `NodeCheck/Builder.lean`) -/

/-- Left-nested sum starting from an accumulator. -/
def addFrom (acc : Nat) : List Nat → HP Nat
  | [] => pure acc
  | y :: ys => do
    let i ← nodeOp 0 acc y
    addFrom i ys

/-- Left-nested product starting from an accumulator. -/
def mulFrom (acc : Nat) : List Nat → HP Nat
  | [] => pure acc
  | y :: ys => do
    let i ← nodeOp 1 acc y
    mulFrom i ys

/-- The sum of a list. -/
def addL : List Nat → HP Nat
  | [] => constant 0
  | x :: xs => addFrom x xs

/-- The product of a list. -/
def mulL : List Nat → HP Nat
  | [] => constant 1
  | x :: xs => mulFrom x xs

/-- `x²`. -/
def square (x : Nat) : HP Nat := mulL [x, x]

/-- `n·x`. -/
def scale (n : Int) (x : Nat) : HP Nat := do
  let c ← constant n
  mulL [c, x]

/-- Run a list of constructions in order. -/
def seqM {α : Type} : List (HP α) → HP (List α)
  | [] => pure []
  | m :: ms => do
    let a ← m
    let as ← seqM ms
    pure (a :: as)

/-- The conjunction of the formulas of a list of constructions. -/
def andM (ms : List (HP LForm)) : HP LForm := do
  let fs ← seqM ms
  pure (.and fs)

/-- `lt(a, b)`. -/
def lt (a b : Nat) : HP LForm := do
  let d ← fresh
  let e ← addL [a, ← constant 1, d]
  pure (.eq b e)

/-- `odd(x)`. -/
def odd (x : Nat) : HP LForm := do
  let h ← fresh
  let e ← addL [← scale 2 h, ← constant 1]
  pure (.eq x e)

/-- `power(P, Q, R)` in hierarchical mode. -/
def power (P Q R : Nat) : HP LForm := callPower P Q R

/-- `binomial(C, N, K)` in hierarchical mode. -/
def binomial (C N K : Nat) : HP LForm := do
  let base ← fresh
  let total ← fresh
  let place ← fresh
  let q ← fresh
  let r ← fresh
  andM [
    do power base (← constant 2) (← addL [N, ← constant 1]),
    do power total (← addL [base, ← constant 1]) N,
    power place base K,
    lt C base,
    lt r place,
    do pure (.eq total (← addL [← mulL [place, ← addL [← mulL [base, q], C]], r]))]

/-- `orthogonal(a, b)` in hierarchical mode. -/
def orthogonal (a b : Nat) : HP LForm := do
  let c ← fresh
  andM [do binomial c (← addL [a, b]) a, odd c]

/-- `mask(a, b)` in hierarchical mode. -/
def mask (a b : Nat) : HP LForm := do
  let c ← fresh
  andM [binomial c b a, odd c]

/-- `bitAnd(z, x, y)` in hierarchical mode. -/
def bitAnd (z x y : Nat) : HP LForm := do
  let a ← fresh
  let b ← fresh
  andM [
    do pure (.eq x (← addL [z, a])),
    do pure (.eq y (← addL [z, b])),
    orthogonal z a,
    orthogonal z b,
    orthogonal a b]

mutual

/-- The node encoding of a formula. -/
def LForm.encode : LForm → HP Nat
  | .eq a b => do addL [a, ← scale (-1) b]
  | .atom f => pure f
  | .call j => pure j
  | .and fs => do
    let es ← LForm.encodeList fs
    let sq ← seqM (es.map square)
    addL sq
  | .or fs => do
    let es ← LForm.encodeList fs
    mulL es

/-- Encodings of a list of formulas, in order. -/
def LForm.encodeList : List LForm → HP (List Nat)
  | [] => pure []
  | f :: fs => do
    let e ← LForm.encode f
    let es ← LForm.encodeList fs
    pure (e :: es)

end

/-! ### Tries and buckets (transcribed from `NodeCheck/Trie.lean` and `NodeCheck/Fast.lean`) -/

/-- Binary tries keyed by natural numbers (a copy of `NodeCheck.NTrie`). -/
inductive LTrie (α : Type) where
  | leaf
  | node (v : Option α) (l r : LTrie α)

namespace LTrie

variable {α : Type}

/-- The value stored at key `k`. -/
def find (t : LTrie α) : Nat → Option α :=
  LTrie.rec (motive := fun _ => Nat → Option α) (fun _ => none)
    (fun v _ _ fl fr k =>
      cond (Nat.beq k 0) v (cond (Nat.beq (Nat.mod k 2) 0) (fl (Nat.div k 2)) (fr (Nat.div k 2))))
    t

/-- One step of insertion. -/
def insStep (g : LTrie α → Nat → α → LTrie α) (t : LTrie α) (k : Nat) (a : α) : LTrie α :=
  LTrie.casesOn (motive := fun _ => LTrie α) t
    (cond (Nat.beq k 0) (node (some a) leaf leaf)
      (cond (Nat.beq (Nat.mod k 2) 0) (node none (g leaf (Nat.div k 2) a) leaf)
        (node none leaf (g leaf (Nat.div k 2) a))))
    (fun v l r => cond (Nat.beq k 0) (node (some a) l r)
      (cond (Nat.beq (Nat.mod k 2) 0) (node v (g l (Nat.div k 2) a) r)
        (node v l (g r (Nat.div k 2) a))))

/-- Store `a` at key `k`, with fuel `f`. -/
def ins (f : Nat) : LTrie α → Nat → α → LTrie α :=
  Nat.rec (motive := fun _ => LTrie α → Nat → α → LTrie α) (fun t _ _ => t)
    (fun _ g t k a => insStep g t k a) f

/-- Store `a` at key `k` (fuel `k + 1`). -/
def insert (t : LTrie α) (k : Nat) (a : α) : LTrie α := t.ins (k + 1) k a

end LTrie

section Buckets

variable {β : Type}

/-- Push `e.2` onto the bucket of key `e.1`. -/
def bucketIns (t : LTrie (List β)) (e : Nat × β) : LTrie (List β) :=
  t.insert e.1 (e.2 :: (t.find e.1).getD [])

/-- Fill the buckets with a list of keyed values, in order (each step forces the trie). -/
def bucketsGo : List (Nat × β) → LTrie (List β) → LTrie (List β)
  | [], t => t
  | e :: l, t =>
    match bucketIns t e with
    | .leaf => bucketsGo l .leaf
    | .node v a b => bucketsGo l (.node v a b)

/-- The buckets of a list of keyed values. -/
def buckets (l : List (Nat × β)) : LTrie (List β) := bucketsGo l .leaf

/-- The values of key `k`, in order. -/
def bucketGet (t : LTrie (List β)) (k : Nat) : List β := ((t.find k).getD []).reverse

end Buckets

/-- The trie of branch histories (the first entry of each index wins). -/
def vwTrie (vw : List (Nat × Nat × Nat)) : LTrie (Nat × Nat) :=
  vw.foldr (fun e t => t.insert e.1 e.2) .leaf

/-- A pass over the program in lockstep with `S`. -/
def pairsGo {β : Type} (zero : Nat) (f : Nat → LInstr → Nat → List (Nat × β)) :
    Nat → List LInstr → List Nat → List (Nat × β)
  | _, [], _ => []
  | i, ins :: p, S => f i ins (S.headD zero) ++ pairsGo zero f (i + 1) p S.tail

/-- Keyed values of `A_j`. -/
def incPairF (_ : Nat) : LInstr → Nat → List (Nat × Nat)
  | .inc j _, s => [(j, s)]
  | _, _ => []

/-- Keyed values of `C_j`. -/
def decPairF (zero : Nat) (vwT : LTrie (Nat × Nat)) (i : Nat) : LInstr → Nat → List (Nat × Nat)
  | .dec j _ _, _ => [(j, ((vwT.find i).getD (zero, zero)).1)]
  | _, _ => []

/-- Keyed values of `I_x`. -/
def inPairF (zero : Nat) (vwT : LTrie (Nat × Nat)) (i : Nat) : LInstr → Nat → List (Nat × Nat)
  | .inc _ x, s => [(x, s)]
  | .dec _ x y, _ => [(x, ((vwT.find i).getD (zero, zero)).1),
      (y, ((vwT.find i).getD (zero, zero)).2)]
  | .halt, _ => []

/-! ### The packed construction (transcribed from `NodeCheck/Packed.lean` and `Fast.lean`) -/

/-- `n` fresh variables, in order. -/
def freshN : Nat → HP (List Nat)
  | 0 => pure []
  | n + 1 => do
    let h ← fresh
    let hs ← freshN n
    pure (h :: hs)

/-- Concatenate the formula lists of constructions run in order. -/
def seqConcat : List (HP (List LForm)) → HP (List LForm)
  | [] => pure []
  | m :: ms => do
    let a ← m
    let b ← seqConcat ms
    pure (a ++ b)

/-- Item 4 for one register. -/
def registerMasks (K D T F Rj Nj : Nat) : HP (List LForm) :=
  seqM [
    mask Rj D,
    lt Rj T,
    do bitAnd (← mulL [K, Nj]) (← addL [Rj, D]) (← mulL [K, F])]

/-- Item 6 for one register. -/
def registerEq (B Rj ιj : Nat) (decs incs : List Nat) : HP LForm := do
  let l ← addL [Rj, ← mulL [B, ← addL decs]]
  let r ← addL [ιj, ← mulL [B, Rj], ← mulL [B, ← addL incs]]
  pure (.eq l r)

/-- Item 7 for one state. -/
def stateEq (B Si e : Nat) (ins : List Nat) : HP LForm := do
  let r ← addL [e, ← mulL [B, ← addL ins]]
  pure (.eq Si r)

/-- Run two formula-list constructions in order and concatenate their formulas. -/
def appendM (m₁ m₂ : HP (List LForm)) : HP (List LForm) := do
  let l₁ ← m₁
  let l₂ ← m₂
  pure (l₁ ++ l₂)

/-- Item 1. -/
def items1 (p : List LInstr) (a : List Nat) (zero q c K B T : Nat) : HP (List LForm) :=
  seqM ([
    lt zero c,
    do power K (← constant 2) c,
    do pure (.eq B (← scale 4 K)),
    do lt (← constant p.length) B,
    power T B q] ++ a.map fun ai => lt ai K)

/-- Item 2. -/
def items2 (zero one K B T F D : Nat) (S : List Nat) : HP (List LForm) :=
  seqM [
    do pure (.eq (← addL [← mulL [B, F], one]) (← addL [F, ← mulL [B, T]])),
    do pure (.eq (← addL [D, F]) (← mulL [K, F])),
    do pure (.eq (← addL S) F),
    pure (.eq (S.getLastD zero) T)]

/-- Item 3. -/
def items3 (F : Nat) (S : List Nat) : HP (List LForm) := seqM (S.map fun x => mask x F)

/-- Item 4. -/
def items4 (r : Nat) (zero K D T F : Nat) (R N : List Nat) : HP (List LForm) :=
  seqConcat ((List.range r).map fun j =>
    registerMasks K D T F (R.getD j zero) (N.getD j zero))

/-- Item 5, walking `S` in lockstep with the instructions. -/
def subBranchesK (zero : Nat) (N : List Nat) :
    Nat → List Nat → List LInstr → HP (List LForm × List (Nat × Nat × Nat))
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

/-- Item 6, with the handles read from buckets. -/
def items6K (p : List LInstr) (r : Nat) (a : List Nat) (zero B : Nat) (R S : List Nat)
    (vw : List (Nat × Nat × Nat)) : HP (List LForm) :=
  let decB := buckets (pairsGo zero (decPairF zero (vwTrie vw)) 0 p S)
  let incB := buckets (pairsGo zero incPairF 0 p S)
  seqM ((List.range r).map fun j =>
    registerEq B (R.getD j zero) (a.getD j zero) (bucketGet decB j) (bucketGet incB j))

/-- The formulas of item 7 for the states `i, …, i + n - 1`, walking `S` in lockstep. -/
def items7Go (zero one B : Nat) (inB : LTrie (List Nat)) : Nat → Nat → List Nat → List (HP LForm)
  | 0, _, _ => []
  | n + 1, i, S =>
    stateEq B (S.headD zero) (bif i.beq 0 then one else zero) (bucketGet inB i) ::
      items7Go zero one B inB n (i + 1) S.tail

/-- Item 7, with the handles read from buckets. -/
def items7K (p : List LInstr) (zero one B : Nat) (S : List Nat) (vw : List (Nat × Nat × Nat)) :
    HP (List LForm) :=
  let inB := buckets (pairsGo zero (inPairF zero (vwTrie vw)) 0 p S)
  seqM (items7Go zero one B inB p.length 0 S)

/-- Items 1–7. -/
def packedFormulasK (p : List LInstr) (r : Nat) (a : List Nat) (zero one q c K B T F D : Nat)
    (R N S : List Nat) : HP (List LForm) :=
  appendM (items1 p a zero q c K B T) <|
  appendM (items2 zero one K B T F D S) <|
  appendM (items3 F S) <|
  appendM (items4 r zero K D T F R N) do
    let sb ← subBranchesK zero N 0 S p
    appendM (pure sb.1) <|
    appendM (items6K p r a zero B R S sb.2) (items7K p zero one B S sb.2)

/-- The packed-history construction. -/
def constructionK (p : List LInstr) (r k : Nat) : HP LForm := do
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

end

end ZInQ.Compiler.NodeSkeleton
