import ZInQKernel.Compiler.NodeCheck.Trie

/-!
# The fast builder

A transcription of the natural construction monad `Natural.NM` and its hierarchical-mode
macros that keeps only what determines the node list: the variable counter, the node list
(stored reversed, with its length) and a hash-consing table (`Table`, a trie keyed by
`nodeKey`). Expressions are node indices and formulas keep only node indices (`FForm`).
Variable nodes are appended without lookup: the variable `X_c` taken by `fresh` is never in the
node list, whose variable nodes all have index below the counter.

`Sim er m m'` says that the construction `m` and the fast construction `m'`, run from related
states (`Rel`: same counter, same node list, the table answers every lookup of a tabled node as
`List.idxOf?` does, every variable node is below the counter), end in related states with
results related by the erasure `er`. Every macro has its fast transcription and its `Sim`
lemma; `sim_tac` proves them step by step.
-/

namespace ZInQ.Compiler.NodeCheck

open Natural

/-- The state of the fast builder. -/
structure FState where
  /-- The variable counter. -/
  next : ℕ
  /-- The hash-consing table of the tabled nodes. -/
  table : Table
  /-- The length of the node list. -/
  len : ℕ
  /-- The node list, reversed. -/
  rev : List NatNode

/-- Fast constructions. -/
def FM (α : Type) : Type := FState → α × FState

namespace FM

instance : Monad FM where
  pure a s := (a, s)
  bind m f s := match m s with
    | (a, s') => f a s'

theorem pure_apply {α : Type} (a : α) (s : FState) : (pure a : FM α) s = (a, s) := rfl

theorem bind_apply {α β : Type} (m : FM α) (f : α → FM β) (s : FState) :
    (m >>= f) s = f (m s).1 (m s).2 := by
  show (match m s with | (a, s') => f a s') = _
  cases m s; rfl

end FM

/-- Formulas of the fast builder: node indices only. -/
inductive FForm
  | eq (a b : ℕ)
  | atom (f : ℕ)
  | call (j : ℕ)
  | and (fs : List FForm)
  | or (fs : List FForm)

mutual

/-- The erasure of a construction formula. -/
def eraseF : NForm → FForm
  | .eq a b => .eq a.node b.node
  | .atom f => .atom f.node
  | .call _ _ _ _ j => .call j
  | .and fs => .and (eraseFs fs)
  | .or fs => .or (eraseFs fs)

/-- The erasure of a list of construction formulas. -/
def eraseFs : List NForm → List FForm
  | [] => []
  | f :: fs => eraseF f :: eraseFs fs

end

theorem eraseFs_eq (fs : List NForm) : eraseFs fs = fs.map eraseF := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [eraseFs, ih]

/-- Variable nodes. -/
def isVarNode : NatNode → Bool
  | .var _ => true
  | _ => false

/-- Related states. Besides the simulation proper, the variable nodes of the construction
are as many as its explicit variables (`vars`). -/
structure Rel (s : State) (t : FState) : Prop where
  next : s.next = t.next
  nodes : s.nodes = t.rev.reverse
  len : t.len = t.rev.length
  find : ∀ n, tabled n = true → t.table.find n = s.nodes.idxOf? n
  var : ∀ i, NatNode.var i ∈ s.nodes → i < s.next
  vars : s.nodes.countP isVarNode = s.vars.length

theorem Rel.of_eq {s s' : State} {t : FState} (h : Rel s t) (h1 : s'.next = s.next)
    (h2 : s'.nodes = s.nodes) (h3 : s'.vars = s.vars) : Rel s' t :=
  ⟨h1 ▸ h.next, h2 ▸ h.nodes, h.len, h2 ▸ h.find, h1 ▸ h2 ▸ h.var, h2 ▸ h3 ▸ h.vars⟩

/-- `m'` simulates `m`, with results related by `er`. -/
structure Sim {α β : Type} (er : α → β) (m : NM α) (m' : FM β) : Prop where
  run : ∀ s t, Rel s t → er (m s).1 = (m' t).1 ∧ Rel (m s).2 (m' t).2

namespace Sim

variable {α β γ δ : Type}

theorem pure {er : α → β} {a : α} {b : β} (h : er a = b) : Sim er (Pure.pure a) (Pure.pure b) :=
  ⟨fun _ _ hr => ⟨h, hr⟩⟩

theorem bind {er : α → β} {er' : γ → δ} {m : NM α} {m' : FM β} {f : α → NM γ}
    {f' : β → FM δ} (hm : Sim er m m') (hf : ∀ a, Sim er' (f a) (f' (er a))) :
    Sim er' (m >>= f) (m' >>= f') := ⟨fun s t hr => by
  obtain ⟨h1, h2⟩ := hm.run s t hr
  obtain ⟨k1, k2⟩ := (hf (m s).1).run _ _ h2
  rw [NM.bind_apply, FM.bind_apply, ← h1]
  exact ⟨k1, k2⟩⟩

theorem note_bind {er : α → β} {k : MacroKind} {m : NM α} {m' : FM β} (h : Sim er m m') :
    Sim er (Natural.note k >>= fun _ => m) m' := ⟨fun _ t hr => h.run _ t (hr.of_eq rfl rfl rfl)⟩

theorem congr_er {er er' : α → β} {m : NM α} {m' : FM β} (h : Sim er m m') (he : er = er') :
    Sim er' m m' := he ▸ h

end Sim

/-! ### Primitives -/

theorem idxOf?_append_singleton (l : List NatNode) (n m : NatNode) :
    (l ++ [n]).idxOf? m = if m ∈ l then l.idxOf? m else if m = n then some l.length else none := by
  unfold List.idxOf?
  rw [List.findIdx?_append]
  by_cases hm : m ∈ l
  · have : (l.findIdx? (· == m)).isSome := by
      rw [← List.idxOf?, List.isSome_idxOf?]; exact hm
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp this
    simp [hm, hj]
  · have : l.findIdx? (· == m) = none := by rw [← List.idxOf?, List.idxOf?_eq_none_iff]; exact hm
    rw [this]
    by_cases h : m = n
    · subst h; simp [hm]
    · simp [hm, h, Ne.symm h]

/-- The index of a tabled node, created if no equal node exists. -/
def node (n : NatNode) : FM ℕ := fun t =>
  match t.table.find n with
  | some j => (j, t)
  | none => (t.len, ⟨t.next, t.table.insert n t.len, t.len + 1, n :: t.rev⟩)

theorem node_sim {n : NatNode} (hn : tabled n = true) : Sim id (Natural.node n) (node n) :=
  ⟨fun s t hr => by
    have hf := hr.find n hn
    unfold Natural.node node
    rw [hf]
    cases h : s.nodes.idxOf? n with
    | some j => exact ⟨rfl, hr⟩
    | none =>
      have hnot : n ∉ s.nodes := List.idxOf?_eq_none_iff.mp h
      refine ⟨by simp [hr.nodes, hr.len],
        ⟨hr.next, by simp [hr.nodes], by simp [hr.len], ?_, ?_, ?_⟩⟩
      · intro m hm
        rw [Table.find_insert _ hn _ hm, idxOf?_append_singleton, hr.find m hm]
        by_cases hmn : m = n
        · subst hmn
          have hnot' : m ∉ t.rev := by simpa [hr.nodes] using hnot
          simp [hnot', hr.nodes, hr.len]
        · by_cases hml : m ∈ s.nodes
          · simp [hml, hmn]
          · simp [hml, hmn, List.idxOf?_eq_none_iff.mpr hml]
      · intro i hi
        rcases List.mem_append.mp hi with hi | hi
        · exact hr.var i hi
        · cases n <;> simp_all [tabled]
      · have : isVarNode n = false := by cases n <;> simp_all [tabled, isVarNode]
        simp [List.countP_append, this, hr.vars]⟩

/-- A fresh variable `X_c`: its variable node is appended. -/
def fresh : FM ℕ := fun t => (t.len, ⟨t.next + 1, t.table, t.len + 1, .var t.next :: t.rev⟩)

theorem fresh_sim : Sim Ex.node Natural.fresh fresh := ⟨fun s t hr => by
  have hnot : NatNode.var s.next ∉ s.nodes := fun h => (Nat.lt_irrefl _ (hr.var _ h))
  have h : s.nodes.idxOf? (.var s.next) = none := List.idxOf?_eq_none_iff.mpr hnot
  simp only [Natural.fresh, Natural.node, h, fresh]
  refine ⟨by simp [hr.nodes, hr.len], ⟨by simp [hr.next], by simp [hr.nodes, hr.next],
    by simp [hr.len], ?_, ?_, ?_⟩⟩
  · intro m hm
    have hmv : m ≠ .var s.next := by rintro rfl; simp [tabled] at hm
    rw [hr.find m hm, idxOf?_append_singleton]
    by_cases hml : m ∈ s.nodes
    · simp [hml]
    · simp [hml, hmv, List.idxOf?_eq_none_iff.mpr hml]
  · intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · have := hr.var i hi; show i < s.next + 1; omega
    · simp only [List.mem_singleton, NatNode.var.injEq] at hi; subst hi; show _ < s.next + 1; omega
  · simp [List.countP_append, isVarNode, hr.vars]⟩

/-- The constant `c`. -/
def constant (c : ℤ) : FM ℕ := node (.const c)

theorem constant_sim (c : ℤ) : Sim Ex.node (Natural.constant c) (constant c) :=
  ⟨fun s t hr => (node_sim (n := .const c) rfl).run s t hr⟩

/-- Left-nested sum starting from an accumulator. -/
def addFrom (acc : ℕ) : List ℕ → FM ℕ
  | [] => pure acc
  | y :: ys => do
    let i ← node (.add acc y)
    addFrom i ys

/-- Left-nested product starting from an accumulator. -/
def mulFrom (acc : ℕ) : List ℕ → FM ℕ
  | [] => pure acc
  | y :: ys => do
    let i ← node (.mul acc y)
    mulFrom i ys

theorem addFrom_sim (acc : Ex) (ys : List Ex) :
    Sim Ex.node (Natural.addFrom acc ys) (addFrom acc.node (ys.map Ex.node)) := by
  induction ys generalizing acc with
  | nil => exact Sim.pure rfl
  | cons y ys ih => exact Sim.bind (node_sim rfl) fun i => ih ⟨i, _⟩

theorem mulFrom_sim (acc : Ex) (ys : List Ex) :
    Sim Ex.node (Natural.mulFrom acc ys) (mulFrom acc.node (ys.map Ex.node)) := by
  induction ys generalizing acc with
  | nil => exact Sim.pure rfl
  | cons y ys ih => exact Sim.bind (node_sim rfl) fun i => ih ⟨i, _⟩

/-- The sum of a list. -/
def addL : List ℕ → FM ℕ
  | [] => constant 0
  | x :: xs => addFrom x xs

/-- The product of a list. -/
def mulL : List ℕ → FM ℕ
  | [] => constant 1
  | x :: xs => mulFrom x xs

theorem addL_sim {xs : List Ex} {ys : List ℕ} (h : xs.map Ex.node = ys) :
    Sim Ex.node (Natural.addL xs) (addL ys) := by
  subst h
  cases xs with
  | nil => exact constant_sim 0
  | cons x xs => exact addFrom_sim x xs

theorem mulL_sim {xs : List Ex} {ys : List ℕ} (h : xs.map Ex.node = ys) :
    Sim Ex.node (Natural.mulL xs) (mulL ys) := by
  subst h
  cases xs with
  | nil => exact constant_sim 1
  | cons x xs => exact mulFrom_sim x xs

/-- `x²`. -/
def square (x : ℕ) : FM ℕ := mulL [x, x]

theorem square_sim {x : Ex} {x' : ℕ} (h : x.node = x') :
    Sim Ex.node (Natural.square x) (square x') := mulL_sim (by simp [h])

/-- `n·x`. -/
def scale (n : ℤ) (x : ℕ) : FM ℕ := do
  let c ← constant n
  mulL [c, x]

theorem scale_sim (n : ℤ) {x : Ex} {x' : ℕ} (h : x.node = x') :
    Sim Ex.node (Natural.scale n x) (scale n x') :=
  Sim.bind (constant_sim n) fun c => mulL_sim (by simp [h])

/-- The call of the power template on a fresh block of `79` variables. -/
def callPower (P Q R : ℕ) : FM FForm := fun t =>
  (.call t.len, ⟨t.next + 79, t.table, t.len + 1, .call P Q R t.next :: t.rev⟩)

theorem callPower_sim {P Q R : Ex} {P' Q' R' : ℕ} (hP : P.node = P') (hQ : Q.node = Q')
    (hR : R.node = R') : Sim eraseF (Natural.callPower P Q R) (callPower P' Q' R') :=
  ⟨fun s t hr => by
    subst hP hQ hR
    simp only [Natural.callPower, callPower, eraseF]
    refine ⟨by simp [hr.nodes, hr.len], ⟨by simp [hr.next, powerWitnesses],
      by simp [hr.nodes, hr.next], by simp [hr.len], ?_, ?_, ?_⟩⟩
    · intro m hm
      have hmv : m ≠ .call P.node Q.node R.node s.next := by rintro rfl; simp [tabled] at hm
      rw [hr.find m hm, idxOf?_append_singleton]
      by_cases hml : m ∈ s.nodes
      · simp [hml]
      · simp [hml, hmv, List.idxOf?_eq_none_iff.mpr hml]
    · intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · have := hr.var i hi; simp only [powerWitnesses]; omega
      · simp at hi
    · simp [List.countP_append, isVarNode, hr.vars]⟩

/-- Run a list of constructions in order. -/
def seqM {α : Type} : List (FM α) → FM (List α)
  | [] => pure []
  | m :: ms => do
    let a ← m
    let as ← seqM ms
    pure (a :: as)

theorem seqM_sim {α β : Type} {er : α → β} :
    ∀ {ms : List (NM α)} {ms' : List (FM β)}, List.Forall₂ (Sim er) ms ms' →
      Sim (List.map er) (Natural.seqM ms) (seqM ms')
  | [], [], .nil => Sim.pure rfl
  | _ :: _, _ :: _, .cons h hs =>
    Sim.bind h fun _ => Sim.bind (seqM_sim hs) fun _ => Sim.pure rfl

/-- The conjunction of the formulas of a list of constructions. -/
def andM (ms : List (FM FForm)) : FM FForm := do
  let fs ← seqM ms
  pure (.and fs)

theorem andM_sim {ms : List (NM NForm)} {ms' : List (FM FForm)}
    (h : List.Forall₂ (Sim eraseF) ms ms') : Sim eraseF (Natural.andM ms) (andM ms') :=
  Sim.bind (seqM_sim h) fun fs => Sim.pure (by simp [eraseF, eraseFs_eq])

/-! ### Gadgets and macros (hierarchical mode) -/

set_option hygiene false in
/-- Proves a `Sim` goal between a construction and its fast transcription, step by step. -/
macro "sim_tac" : tactic => `(tactic| repeat' (first
  | rfl
  | (intro _)
  | (with_reducible apply Sim.note_bind)
  | (with_reducible apply Sim.pure)
  | (with_reducible apply List.Forall₂.nil)
  | (with_reducible apply List.Forall₂.cons)
  | (with_reducible apply fresh_sim)
  | (with_reducible apply constant_sim)
  | (with_reducible apply addL_sim)
  | (with_reducible apply mulL_sim)
  | (with_reducible apply square_sim)
  | (with_reducible apply scale_sim)
  | (with_reducible apply callPower_sim)
  | (with_reducible apply andM_sim)
  | (with_reducible apply seqM_sim)
  | (with_reducible apply lt_sim)
  | (with_reducible apply odd_sim)
  | (with_reducible apply power_sim)
  | (with_reducible apply binomial_sim)
  | (with_reducible apply orthogonal_sim)
  | (with_reducible apply mask_sim)
  | (with_reducible apply bitAnd_sim)
  | (with_reducible apply Sim.bind)))

/-- `lt(a, b)`. -/
def lt (a b : ℕ) : FM FForm := do
  let d ← fresh
  let e ← addL [a, ← constant 1, d]
  pure (.eq b e)

theorem lt_sim {a b : Ex} {a' b' : ℕ} (ha : a.node = a') (hb : b.node = b') :
    Sim eraseF (Natural.lt a b) (lt a' b') := by
  subst ha hb
  unfold Natural.lt lt
  sim_tac

/-- `odd(x)`. -/
def odd (x : ℕ) : FM FForm := do
  let h ← fresh
  let e ← addL [← scale 2 h, ← constant 1]
  pure (.eq x e)

theorem odd_sim {x : Ex} {x' : ℕ} (hx : x.node = x') : Sim eraseF (Natural.odd x) (odd x') := by
  subst hx
  unfold Natural.odd odd
  sim_tac

/-- `power(P, Q, R)` in hierarchical mode. -/
def power (P Q R : ℕ) : FM FForm := callPower P Q R

theorem power_sim {P Q R : Ex} {P' Q' R' : ℕ} (hP : P.node = P') (hQ : Q.node = Q')
    (hR : R.node = R') : Sim eraseF (Natural.power .hierarchical P Q R) (power P' Q' R') :=
  Sim.note_bind (callPower_sim hP hQ hR)

/-- `binomial(C, N, K)` in hierarchical mode. -/
def binomial (C N K : ℕ) : FM FForm := do
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

theorem binomial_sim {C N K : Ex} {C' N' K' : ℕ} (hC : C.node = C') (hN : N.node = N')
    (hK : K.node = K') :
    Sim eraseF (Natural.binomial .hierarchical C N K) (binomial C' N' K') := by
  subst hC hN hK
  unfold Natural.binomial binomial
  sim_tac

/-- `orthogonal(a, b)` in hierarchical mode. -/
def orthogonal (a b : ℕ) : FM FForm := do
  let c ← fresh
  andM [do binomial c (← addL [a, b]) a, odd c]

theorem orthogonal_sim {a b : Ex} {a' b' : ℕ} (ha : a.node = a') (hb : b.node = b') :
    Sim eraseF (Natural.orthogonal .hierarchical a b) (orthogonal a' b') := by
  subst ha hb
  unfold Natural.orthogonal orthogonal
  sim_tac

/-- `mask(a, b)` in hierarchical mode. -/
def mask (a b : ℕ) : FM FForm := do
  let c ← fresh
  andM [binomial c b a, odd c]

theorem mask_sim {a b : Ex} {a' b' : ℕ} (ha : a.node = a') (hb : b.node = b') :
    Sim eraseF (Natural.mask .hierarchical a b) (mask a' b') := by
  subst ha hb
  unfold Natural.mask mask
  sim_tac

/-- `bitAnd(z, x, y)` in hierarchical mode. -/
def bitAnd (z x y : ℕ) : FM FForm := do
  let a ← fresh
  let b ← fresh
  andM [
    do pure (.eq x (← addL [z, a])),
    do pure (.eq y (← addL [z, b])),
    orthogonal z a,
    orthogonal z b,
    orthogonal a b]

theorem bitAnd_sim {z x y : Ex} {z' x' y' : ℕ} (hz : z.node = z') (hx : x.node = x')
    (hy : y.node = y') : Sim eraseF (Natural.bitAnd .hierarchical z x y) (bitAnd z' x' y') := by
  subst hz hx hy
  unfold Natural.bitAnd bitAnd
  sim_tac

/-! ### Node encoding of formulas -/

mutual

/-- The node encoding of a formula. -/
def FForm.encode : FForm → FM ℕ
  | .eq a b => do addL [a, ← scale (-1) b]
  | .atom f => pure f
  | .call j => pure j
  | .and fs => do
    let es ← FForm.encodeList fs
    let sq ← seqM (es.map square)
    addL sq
  | .or fs => do
    let es ← FForm.encodeList fs
    mulL es

/-- Encodings of a list of formulas, in order. -/
def FForm.encodeList : List FForm → FM (List ℕ)
  | [] => pure []
  | f :: fs => do
    let e ← FForm.encode f
    let es ← FForm.encodeList fs
    pure (e :: es)

end

theorem forall₂_map_square (es : List Ex) :
    List.Forall₂ (Sim Ex.node) (es.map Natural.square) ((es.map Ex.node).map square) := by
  induction es with
  | nil => exact .nil
  | cons e es ih => exact .cons (square_sim rfl) ih

mutual

theorem encode_sim (τ : Syntax.ExPoly) : ∀ φ : NForm,
    Sim Ex.node (φ.encode τ) (eraseF φ).encode
  | .eq _ _ => Sim.bind (scale_sim (-1) rfl) fun _ => addL_sim rfl
  | .atom _ => Sim.pure rfl
  | .call _ _ _ _ _ => Sim.pure rfl
  | .and fs => Sim.bind (encodeList_sim τ fs) fun es =>
      Sim.bind (seqM_sim (forall₂_map_square es)) fun _ => addL_sim rfl
  | .or fs => Sim.bind (encodeList_sim τ fs) fun _ => mulL_sim rfl

theorem encodeList_sim (τ : Syntax.ExPoly) : ∀ fs : List NForm,
    Sim (List.map Ex.node) (NForm.encodeList τ fs) (FForm.encodeList (eraseFs fs))
  | [] => Sim.pure rfl
  | f :: fs => Sim.bind (encode_sim τ f) fun _ =>
      Sim.bind (encodeList_sim τ fs) fun _ => Sim.pure rfl

end

end ZInQ.Compiler.NodeCheck
