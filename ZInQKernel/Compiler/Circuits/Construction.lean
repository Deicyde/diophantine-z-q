import ZInQKernel.Syntax.Language

/-!
# Natural constructions and their macros

A natural construction keeps a variable counter, a list of explicit variables (index and
kind, the inputs first), a hash-consed node list and the list of power-call blocks. It is a
program in the state monad `Natural.NM`, a transcription of the `Builder` class of
`construction/integer-diophantine-compiler.js`:

* `node n` returns the index of the node `n`, creating it only if no equal node exists;
* `constant c`, `addL xs`, `mulL xs`, `square x`, `scale n x` build expressions (sums and
  products of lists are left-nested, the empty sum is the constant `0` and the empty product
  the constant `1`, `n·x` is the product node of the constant `n` and `x`, `x²` is `x·x`);
* `fresh` takes a fresh variable `X_c` (recorded as an explicit witness), `c ↦ c + 1`;
* `callPower P Q R` (hierarchical mode) takes the block `X_c, …, X_{c+78}`, `c ↦ c + 79`, and
  returns the atom `⟨𝒫[P, Q, R; c]⟩`;
* `note k` records the gadget or macro `k` in the log (the builder's `macroCounts`).

An expression is handled through `Ex`: its node index together with the polynomial it
stands for. Formulas `NForm` have atoms `a ≐ b`, `⟨f⟩` and call atoms, and n-ary
conjunctions and disjunctions; `NForm.toFormula τ` reads them as formulas of the
specification chapter (`ZInQ.Syntax.Formula`), the call atoms calling `τ`.

The gadgets `lt`, `divides`, `congruent`, `odd` and the macros `alpha`, `power`, `binomial`,
`orthogonal`, `mask`, `bitAnd` take their fresh variables in the order listed in the
blueprint, and create their nodes in the order of the JavaScript builder (arguments are
evaluated left to right before the body runs). `NForm.encode` is the node encoding of a
formula (`a ≐ b` becomes `a + (-1)·b`, a conjunction the sum of the squares, a disjunction
the product).

(Blueprint: `compiler/natural/formulas/natural-constructions.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Natural

open Syntax MvPolynomial

/-- Nodes of a natural circuit: constants, variables, sums, products and calls
`call a b c w` of the power template on the nodes `a, b, c` with block start `w`. -/
inductive NatNode
  | const (c : ℤ)
  | var (i : ℕ)
  | add (j k : ℕ)
  | mul (j k : ℕ)
  | call (a b c w : ℕ)
  deriving DecidableEq, Repr

/-- Kinds of explicit variables. -/
inductive VarKind
  | input
  | witness
  deriving DecidableEq, Repr

/-- An expression: a node index and the polynomial it stands for. -/
structure Ex where
  /-- The node index. -/
  node : ℕ
  /-- The polynomial. -/
  poly : Poly

/-- Formulas of a natural construction. -/
inductive NForm
  /-- The atom `a ≐ b`. -/
  | eq (a b : Ex)
  /-- The atom `⟨f⟩`. -/
  | atom (f : Ex)
  /-- The call atom `⟨𝒫[P, Q, R; w]⟩`, with the index of its call node. -/
  | call (P Q R : Ex) (w : ℕ) (node : ℕ)
  /-- The conjunction. -/
  | and (fs : List NForm)
  /-- The disjunction. -/
  | or (fs : List NForm)

/-- The parameter polynomials of a call, as a function on `Fin p` (missing entries `0`). -/
def callArgs (P Q R : Poly) (p : ℕ) : Fin p → Poly := fun i => getPoly [P, Q, R] i

/-- Reading of a construction formula as a formula of the specification chapter; call atoms
call `τ`. -/
def NForm.toFormula (τ : ExPoly) : NForm → Formula
  | .eq a b => .eq a.poly b.poly
  | .atom f => .atom f.poly
  | .call P Q R w _ => .call τ (callArgs P.poly Q.poly R.poly τ.params) w
  | .and fs => .and (fs.map (toFormula τ))
  | .or fs => .or (fs.map (toFormula τ))

/-- The kinds of gadgets and macros, recorded in the construction log (as the JavaScript
builder's `macroCounts`). -/
inductive MacroKind
  | lt
  | divides
  | congruent
  | odd
  | alpha
  | power
  | binomial
  | orthogonal
  | mask
  | bitAnd
  deriving DecidableEq, Repr

/-- The state of a natural construction. -/
structure State where
  /-- The variable counter. -/
  next : ℕ
  /-- The explicit variables, in allocation order. -/
  vars : List (ℕ × VarKind)
  /-- The hash-consed node list. -/
  nodes : List NatNode
  /-- The block starts of the power calls, in allocation order. -/
  blocks : List ℕ
  /-- The gadgets and macros run so far, in order. -/
  log : List MacroKind := []

/-- Natural constructions. -/
def NM (α : Type) : Type := State → α × State

namespace NM

instance : Monad NM where
  pure a s := (a, s)
  bind m f s := f (m s).1 (m s).2

@[simp] theorem pure_apply {α : Type} (a : α) (s : State) : (pure a : NM α) s = (a, s) := rfl

@[simp] theorem bind_apply {α β : Type} (m : NM α) (f : α → NM β) (s : State) :
    (m >>= f) s = f (m s).1 (m s).2 := rfl

end NM

/-! ### Builder operations -/

/-- The witness count of the power template. -/
def powerWitnesses : ℕ := 79

/-- The index of the node `n`, created if no equal node exists (hash-consing). -/
def node (n : NatNode) : NM ℕ := fun s =>
  match s.nodes.idxOf? n with
  | some j => (j, s)
  | none => (s.nodes.length, { s with nodes := s.nodes ++ [n] })

/-- Record a gadget or macro in the log. -/
def note (k : MacroKind) : NM Unit := fun s => ((), { s with log := s.log ++ [k] })

/-- The constant `c`. -/
def constant (c : ℤ) : NM Ex := do
  let i ← node (.const c)
  pure ⟨i, C c⟩

/-- A fresh variable `X_c`, recorded as an explicit witness. -/
def fresh : NM Ex := fun s =>
  let r := node (.var s.next)
    { s with next := s.next + 1, vars := s.vars ++ [(s.next, .witness)] }
  (⟨r.1, X s.next⟩, r.2)

/-- Left-nested sum starting from an accumulator. -/
def addFrom (acc : Ex) : List Ex → NM Ex
  | [] => pure acc
  | y :: ys => do
    let i ← node (.add acc.node y.node)
    addFrom ⟨i, acc.poly + y.poly⟩ ys

/-- Left-nested product starting from an accumulator. -/
def mulFrom (acc : Ex) : List Ex → NM Ex
  | [] => pure acc
  | y :: ys => do
    let i ← node (.mul acc.node y.node)
    mulFrom ⟨i, acc.poly * y.poly⟩ ys

/-- The sum of a list (left-nested; the empty sum is the constant `0`). -/
def addL : List Ex → NM Ex
  | [] => constant 0
  | x :: xs => addFrom x xs

/-- The product of a list (left-nested; the empty product is the constant `1`). -/
def mulL : List Ex → NM Ex
  | [] => constant 1
  | x :: xs => mulFrom x xs

/-- `x²`, the product node `x·x`. -/
def square (x : Ex) : NM Ex := mulL [x, x]

/-- `n·x`, the product node of the constant `n` and `x`. -/
def scale (n : ℤ) (x : Ex) : NM Ex := do
  let c ← constant n
  mulL [c, x]

/-- The call of the power template on `P, Q, R` with a fresh block of `79` variables. -/
def callPower (P Q R : Ex) : NM NForm := fun s =>
  (.call P Q R s.next s.nodes.length,
    { s with next := s.next + powerWitnesses,
             nodes := s.nodes ++ [.call P.node Q.node R.node s.next],
             blocks := s.blocks ++ [s.next] })

/-- Run a list of constructions in order. -/
def seqM {α : Type} : List (NM α) → NM (List α)
  | [] => pure []
  | m :: ms => do
    let a ← m
    let as ← seqM ms
    pure (a :: as)

/-- The conjunction of the formulas of a list of constructions, run in order. -/
def andM (ms : List (NM NForm)) : NM NForm := do
  let fs ← seqM ms
  pure (.and fs)

/-- The disjunction of the formulas of a list of constructions, run in order. -/
def orM (ms : List (NM NForm)) : NM NForm := do
  let fs ← seqM ms
  pure (.or fs)

/-! ### Gadgets and macros -/

/-- `lt(a, b)`: fresh `d`; the atom `b ≐ a + 1 + d`. -/
def lt (a b : Ex) : NM NForm := do
  note .lt
  let d ← fresh
  let e ← addL [a, ← constant 1, d]
  pure (.eq b e)

/-- `divides(a, b)`: fresh `d`; the atom `b ≐ a·d`. -/
def divides (a b : Ex) : NM NForm := do
  note .divides
  let d ← fresh
  let e ← mulL [a, d]
  pure (.eq b e)

/-- `congruent(a, M, b)`: fresh `u, v`; the atom `a + M u ≐ b + M v`. -/
def congruent (a M b : Ex) : NM NForm := do
  note .congruent
  let u ← fresh
  let v ← fresh
  let l ← addL [a, ← mulL [M, u]]
  let r ← addL [b, ← mulL [M, v]]
  pure (.eq l r)

/-- `odd(x)`: fresh `h`; the atom `x ≐ 2h + 1`. -/
def odd (x : Ex) : NM NForm := do
  note .odd
  let h ← fresh
  let e ← addL [← scale 2 h, ← constant 1]
  pure (.eq x e)

/-- `alpha(X, b, N)`: fresh `r, s, t, u, v, w, x, y`; the fifteen conditions (C.2). -/
def alpha (X b N : Ex) : NM NForm := do
  note .alpha
  let r ← fresh
  let s ← fresh
  let t ← fresh
  let u ← fresh
  let v ← fresh
  let w ← fresh
  let x ← fresh
  let y ← fresh
  let one ← constant 1
  let two ← constant 2
  andM [
    do lt (← constant 3) b,
    do pure (.eq (← addL [one, ← mulL [b, u, t]]) (← addL [← square u, ← square t])),
    do pure (.eq (← addL [one, ← mulL [b, s, r]]) (← addL [← square s, ← square r])),
    lt r s,
    do divides (← square u) s,
    do pure (.eq (← addL [v, ← scale 2 r]) (← mulL [b, s])),
    congruent b v w,
    congruent two u w,
    lt two w,
    do pure (.eq (← addL [one, ← mulL [w, x, y]]) (← addL [← square x, ← square y])),
    do lt (← scale 2 X) u,
    do lt (← scale 2 X) v,
    congruent x v X,
    do lt (← scale 2 N) u,
    congruent x u N]

/-- The flat power macro: fresh `b, m, a₀, a₁, a₂`; the disjunction of the three branches of
the power formula (C.3). -/
def powerFlat (P Q R : Ex) : NM NForm := do
  let zero ← constant 0
  let one ← constant 1
  let b ← fresh
  let m ← fresh
  let a0 ← fresh
  let a1 ← fresh
  let a2 ← fresh
  orM [
    andM [pure (.eq Q zero), pure (.eq R zero), pure (.eq P one)],
    andM [pure (.eq Q zero), lt zero R, pure (.eq P zero)],
    andM [
      lt zero Q,
      do alpha a0 (← addL [Q, ← constant 4]) (← addL [R, one]),
      do pure (.eq b (← addL [a0, ← square Q, ← constant 2])),
      do pure (.eq (← addL [m, ← square Q, one]) (← mulL [b, Q])),
      lt P m,
      alpha a1 b R,
      do alpha a2 b (← addL [R, one]),
      do congruent (← addL [P, ← mulL [b, a1]]) m (← addL [← mulL [Q, a1], a2])]]

/-- The two readings of the power macro. -/
inductive PowerMode
  /-- The flat macro. -/
  | flat
  /-- A call of the power template on a fresh block. -/
  | hierarchical
  deriving DecidableEq, Repr

/-- `power(P, Q, R)` in the given mode. -/
def power (mode : PowerMode) (P Q R : Ex) : NM NForm := do
  note .power
  match mode with
  | .flat => powerFlat P Q R
  | .hierarchical => callPower P Q R

/-- `binomial(C, N, K)`: fresh `β, τ, π, q, r`; three powers, two strict inequalities and the
digit equation. -/
def binomial (mode : PowerMode) (C N K : Ex) : NM NForm := do
  note .binomial
  let base ← fresh
  let total ← fresh
  let place ← fresh
  let q ← fresh
  let r ← fresh
  andM [
    do power mode base (← constant 2) (← addL [N, ← constant 1]),
    do power mode total (← addL [base, ← constant 1]) N,
    power mode place base K,
    lt C base,
    lt r place,
    do pure (.eq total (← addL [← mulL [place, ← addL [← mulL [base, q], C]], r]))]

/-- `orthogonal(a, b)`: fresh `c`; `binomial(c, a + b, a)` and `odd(c)`. -/
def orthogonal (mode : PowerMode) (a b : Ex) : NM NForm := do
  note .orthogonal
  let c ← fresh
  andM [do binomial mode c (← addL [a, b]) a, odd c]

/-- `mask(a, b)`: fresh `c`; `binomial(c, b, a)` and `odd(c)`. -/
def mask (mode : PowerMode) (a b : Ex) : NM NForm := do
  note .mask
  let c ← fresh
  andM [binomial mode c b a, odd c]

/-- `bitAnd(z, x, y)`: fresh `a, b`; `x ≐ z + a`, `y ≐ z + b` and three orthogonalities. -/
def bitAnd (mode : PowerMode) (z x y : Ex) : NM NForm := do
  note .bitAnd
  let a ← fresh
  let b ← fresh
  andM [
    do pure (.eq x (← addL [z, a])),
    do pure (.eq y (← addL [z, b])),
    orthogonal mode z a,
    orthogonal mode z b,
    orthogonal mode a b]

/-! ### Node encoding of formulas -/

mutual

/-- The node encoding of a formula: `a ≐ b` becomes `a + (-1)·b`, `⟨f⟩` is `f`, a call atom
is its call node, a conjunction is the left-nested sum of the squares of the encodings of its
members and a disjunction the left-nested product. -/
def NForm.encode (τ : ExPoly) : NForm → NM Ex
  | .eq a b => do addL [a, ← scale (-1) b]
  | .atom f => pure f
  | .call P Q R w j => pure ⟨j, τ.call (callArgs P.poly Q.poly R.poly τ.params) w⟩
  | .and fs => do
    let es ← NForm.encodeList τ fs
    let sq ← seqM (es.map square)
    addL sq
  | .or fs => do
    let es ← NForm.encodeList τ fs
    mulL es

/-- Encodings of a list of formulas, in order. -/
def NForm.encodeList (τ : ExPoly) : List NForm → NM (List Ex)
  | [] => pure []
  | f :: fs => do
    let e ← NForm.encode τ f
    let es ← NForm.encodeList τ fs
    pure (e :: es)

end

end ZInQ.Compiler.Natural
