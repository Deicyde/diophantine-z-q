import ZInQKernel.Size.Majorants.Calculus

/-!
# The tactic `size`

`size` proves a goal `Sz B ?e ?s P` (or `PSz`, `ASz`, `FAll`) whose levels are metavariables:
it applies the rules of `ZInQKernel.Size.Majorants.Calculus` by the head symbol of the
subject, from the root to the leaves, and the leaves fix the levels. The levels it produces
are closed expressions built from numerals, `max`, `+` and `*`, compared with the target by
`decide` afterwards.

The tactic unfolds the definitions of formulas, pairs and codes it does not know, uses the
hypotheses of the context for callees and constructors (`Sz B e s τ.poly`,
`∀ c, Sz B e s (I.psi n c)`, …), and closes numeric side conditions (bounds on constants and
exponents, list lengths) by `decide`. It never unfolds the polynomial of a template.
-/

namespace ZInQ.Size.Tac

open MvPolynomial ZInQ.Syntax

/-! ### Rules with their numeric parameter first -/

theorem C (k : ℕ) {B : ℕ} {σ : Type*} (hB : 1 ≤ B) {c : ℤ} (hc : c.natAbs ≤ 2 ^ 2 ^ k) :
    Sz B 0 k (MvPolynomial.C c : MvPolynomial σ ℤ) := Sz.C hB hc

theorem intCast (k : ℕ) {B : ℕ} {σ : Type*} (hB : 1 ≤ B) {c : ℤ} (hc : c.natAbs ≤ 2 ^ 2 ^ k) :
    Sz B 0 k (c : MvPolynomial σ ℤ) := Sz.intCast hB hc

theorem ofNat (k : ℕ) {B : ℕ} {σ : Type*} (hB : 1 ≤ B) (n : ℕ) [n.AtLeastTwo]
    (hn : n ≤ 2 ^ 2 ^ k) : Sz B 0 k (OfNat.ofNat n : MvPolynomial σ ℤ) := Sz.ofNat hB n hn

theorem pow (k : ℕ) {B e s : ℕ} {σ : Type*} {P : MvPolynomial σ ℤ} {n : ℕ} (hP : Sz B e s P)
    (hn : n ≤ 2 ^ k) : Sz B e (s + k) (P ^ n) := hP.pow hn

theorem ppow (m : ℕ) {B e s : ℕ} (hB : 1 ≤ B) {u : Pair} {n : ℕ} (hn : n < 2 ^ m)
    (hu : PSz B e s u) : PSz B e (s + 3 * m) (u.pow n) := PSz.pow hB m hn hu

theorem ofInt (k : ℕ) {B : ℕ} (hB : 1 ≤ B) {a b : ℤ} (ha : a.natAbs ≤ 2 ^ 2 ^ k)
    (hb : b.natAbs ≤ 2 ^ 2 ^ k) : PSz B 0 k (Pair.ofInt a b) := PSz.ofInt' hB k ha hb

theorem and (k : ℕ) {B e s : ℕ} (hB : 1 ≤ B) {fs : List Formula} (hfs : FAll B e s fs)
    (hlen : fs.length ≤ 2 ^ k) : Sz B e (s + 1 + k) (Formula.and fs).compile :=
  Sz.compile_and' hB k hfs hlen

theorem or (k : ℕ) {B e s : ℕ} {fs : List Formula} (hfs : FAll B e s fs)
    (hlen : fs.length ≤ 2 ^ k) : Sz B e (s + k) (Formula.or fs).compile :=
  Sz.compile_or' k hfs hlen

theorem ofFn {B e s n : ℕ} {f : Fin n → Formula} (h : ∀ i, Sz B e s (f i).compile) :
    FAll B e s (List.ofFn f) := by
  intro φ hφ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
  exact h i

theorem pairs {B e s n : ℕ} {D : Fin n → Pair} (h : ∀ i, PSz B e s (D i)) :
    ASz B e s (pairsArgs D) := by
  intro k
  unfold pairsArgs
  split_ifs
  exacts [(h _).1, (h _).2]

/-! ### The tactic -/

open Lean Elab Tactic Meta

/-- Close a side condition: by assumption (`1 ≤ B`) or by `decide`. -/
def sideGoal (g : MVarId) : TacticM Unit := g.withContext do
  if (← observing? (withReducible g.assumption)).isSome then return
  let saved ← getGoals
  setGoals [g]
  try
    withoutRecover <| evalTactic (← `(tactic|
      first | exact Nat.le_of_ble_eq_true rfl | decide | (simp; done)))
  finally
    setGoals saved

/-- The smallest `k` with `n ≤ 2^k`. -/
def ceilLog2 (n : ℕ) : ℕ := Id.run do
  let mut k := 0
  while 2 ^ k < n do
    k := k + 1
  return k

def isStructural (tgt : Expr) : Bool :=
  let fn := tgt.getAppFn
  fn.isConstOf ``Sz || fn.isConstOf ``PSz || fn.isConstOf ``ASz || fn.isConstOf ``FAll

mutual

/-- Apply the lemma `e` to `g`, close the side conditions, then solve the structural goals. -/
partial def applyThen (g : MVarId) (e : Expr) : TacticM Unit := do
  let gs ← g.apply e
  let mut structural := #[]
  for g' in gs do
    if ← g'.isAssigned then continue
    let ty ← instantiateMVars (← g'.getType)
    if (← isProp ty) then
      if isStructural ty.cleanupAnnotations || ty.isForall then
        structural := structural.push g'
      else
        sideGoal g'
  for g' in structural do
    sizeGoal g'

/-- Try the lemmas in order (with backtracking on failures). -/
partial def tryLemmas (g : MVarId) (es : List (TacticM Expr)) : TacticM Unit := do
  match es with
  | [] => throwError "size: no rule applies to{indentExpr (← g.getType)}"
  | e :: es =>
    let saved ← saveState
    try
      applyThen g (← e)
    catch ex =>
      if es.isEmpty then throw ex
      saved.restore
      tryLemmas g es

/-- Replace the subject (argument `k`) of the goal by its unfolding and retry. -/
partial def unfoldSubject (g : MVarId) (tgt : Expr) (k : ℕ) : TacticM Unit := do
  let fn := tgt.getAppFn
  let args := tgt.getAppArgs
  let e ← whnfCore args[k]!
  if let some e' ← unfoldDefinition? e then
    let g' ← g.replaceTargetDefEq (mkAppN fn (args.set! k e'))
    sizeGoal g'
  else
    throwError "size: cannot handle{indentExpr tgt}"

partial def sizeGoal (g : MVarId) : TacticM Unit := g.withContext do
  if ← g.isAssigned then return
  let tgt := (← instantiateMVars (← g.getType)).cleanupAnnotations.headBeta
  if tgt.isForall then
    if !(← isProp tgt.bindingDomain!) then
      let (_, g') ← g.intro1
      sizeGoal g'
      return
  unless isStructural tgt do
    sideGoal g
    return
  if (← observing? (withReducible g.assumption)).isSome then return
  -- universally quantified hypotheses (constructor bounds)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty := (← instantiateMVars d.type).cleanupAnnotations
    if ty.isForall && isStructural ty.getForallBody then
      let saved ← saveState
      try
        let gs ← withReducible (g.apply d.toExpr)
        for g' in gs do sizeGoal g'
        return
      catch _ => saved.restore
  let fn := tgt.getAppFn
  let args := tgt.getAppArgs
  let c (n : Name) : TacticM Expr := mkConstWithFreshMVarLevels n
  let cn (n : Name) (k : ℕ) : TacticM Expr := do return mkApp (← c n) (mkNatLit k)
  if fn.isConstOf ``Sz then
    let P ← whnfCore args[4]!
    let head := P.getAppFn
    match head.constName? with
    | some ``HAdd.hAdd => applyThen g (← c ``Sz.add')
    | some ``HSub.hSub => applyThen g (← c ``Sz.sub')
    | some ``HMul.hMul => applyThen g (← c ``Sz.mul')
    | some ``Neg.neg => applyThen g (← c ``Sz.neg')
    | some ``HPow.hPow =>
      let some n ← (evalNat (P.getArg! 5)).run | throwError "size: exponent is not a numeral{indentExpr P}"
      applyThen g (← cn ``Tac.pow (ceilLog2 n))
    | some ``MvPolynomial.X => applyThen g (← c ``Sz.X')
    | some ``Int.cast => tryLemmas g ([0, 3, 5, 7].map fun k => cn ``Tac.intCast k)
    | some ``OfNat.ofNat =>
      match (P.getArg! 1).rawNatLit? with
      | some 0 => applyThen g (← c ``Sz.zero')
      | some 1 => applyThen g (← c ``Sz.one')
      | _ => tryLemmas g ([0, 3, 5, 7].map fun k => cn ``Tac.ofNat k)
    | some ``Zero.zero => applyThen g (← c ``Sz.zero')
    | some ``One.one => applyThen g (← c ``Sz.one')
    | some ``Formula.compile =>
      let φ ← whnfCore P.appArg!
      match φ.getAppFn.constName? with
      | some ``Formula.eq => applyThen g (← c ``Sz.compile_eq')
      | some ``Formula.atom => applyThen g (← c ``Sz.compile_atom')
      | some ``Formula.call => applyThen g (← c ``Sz.compile_call')
      | some ``Formula.and => tryLemmas g ([1, 2, 3, 4, 5, 6, 7].map fun k => cn ``Tac.and k)
      | some ``Formula.or => tryLemmas g ([1, 2, 3].map fun k => cn ``Tac.or k)
      | _ =>
        if let some φ' ← unfoldDefinition? φ then
          let P' := mkApp P.appFn! φ'
          let g' ← g.replaceTargetDefEq (mkAppN fn (args.set! 4 P'))
          sizeGoal g'
        else throwError "size: cannot handle the formula{indentExpr φ}"
    | some ``ExPoly.call => applyThen g (← c ``Sz.call')
    | some ``Pair.norm => applyThen g (← c ``PSz.norm')
    | some ``Prod.fst => applyThen g (← c ``PSz.fst)
    | some ``Prod.snd => applyThen g (← c ``PSz.snd)
    | some ``DFunLike.coe =>
      if P.getAppNumArgs == 6 && (P.getArg! 4).isAppOf ``MvPolynomial.C then
        tryLemmas g ([0, 3, 5, 7].map fun k => cn ``Tac.C k)
      else if P.getAppNumArgs == 6 && (P.getArg! 4).isAppOf ``MvPolynomial.bind₁ then
        applyThen g (← c ``Sz.bind₁_fin)
      else throwError "size: cannot handle{indentExpr P}"
    | _ =>
      -- an entry `g k` of an argument tuple
      if P.isApp then
        let fType ← whnf (← inferType P.appFn!)
        if fType.isForall && fType.bindingDomain!.isAppOf ``Fin then
          applyThen g (← c ``Sz.app)
          return
      unfoldSubject g tgt 4
  else if fn.isConstOf ``PSz then
    let u ← whnfCore args[3]!
    match u.getAppFn.constName? with
    | some ``Pair.mul => applyThen g (← c ``PSz.mul')
    | some ``Pair.sq => applyThen g (← c ``PSz.sq')
    | some ``Pair.add => applyThen g (← c ``PSz.add')
    | some ``Pair.sub => applyThen g (← c ``PSz.sub')
    | some ``Pair.neg => applyThen g (← c ``PSz.neg')
    | some ``Pair.smul => applyThen g (← c ``PSz.smul')
    | some ``Pair.conj => applyThen g (← c ``PSz.conj')
    | some ``Pair.pow =>
      let some n ← (evalNat u.appArg!).run | throwError "size: exponent is not a numeral{indentExpr u}"
      applyThen g (← cn ``Tac.ppow (ceilLog2 (n + 1)))
    | some ``Pair.ofInt => tryLemmas g ([0, 3, 5, 7].map fun k => cn ``Tac.ofInt k)
    | some ``Prod.mk => applyThen g (← c ``PSz.mk')
    | some ``varPair => applyThen g (← c ``PSz.varPair)
    | some ``Code.x => applyThen g (← c ``PSz.x)
    | some ``Code.y => applyThen g (← c ``PSz.y)
    | some ``slopeW => applyThen g (← c ``PSz.slopeW')
    | some ``Pair.log25 => applyThen g (← c ``PSz.log25')
    | _ => unfoldSubject g tgt 3
  else if fn.isConstOf ``ASz then
    let a ← whnfCore args[4]!
    match a.getAppFn.constName? with
    | some ``Fin.append => applyThen g (← c ``ASz.append')
    | some ``Matrix.vecCons => applyThen g (← c ``ASz.cons')
    | some ``Matrix.vecEmpty => applyThen g (← c ``ASz.nil)
    | some ``varPoint => applyThen g (← c ``ASz.varPoint)
    | some ``varArgs => applyThen g (← c ``ASz.varArgs)
    | some ``Code.neg => applyThen g (← c ``ASz.neg)
    | some ``Code.O => applyThen g (← c ``ASz.O)
    | some ``Pair.args => applyThen g (← c ``PSz.args)
    | some ``codesArgs => applyThen g (← c ``ASz.codes)
    | some ``pairsArgs => applyThen g (← c ``Tac.pairs)
    | _ =>
      if a.isLambda then
        let (_, g') ← g.intro1
        sizeGoal g'
      else unfoldSubject g tgt 4
  else
    -- `FAll`
    let l ← whnfR args[3]!
    match l.getAppFn.constName? with
    | some ``List.cons => applyThen g (← c ``FAll.cons')
    | some ``List.nil => applyThen g (← c ``FAll.nil)
    | some ``HAppend.hAppend => applyThen g (← c ``FAll.append')
    | some ``List.ofFn => applyThen g (← c ``Tac.ofFn)
    | _ => unfoldSubject g tgt 3

end

/-- Prove a size goal `Sz B ?e ?s P` (or `PSz`, `ASz`, `FAll`) with metavariable levels. -/
elab "size" : tactic => do
  let g ← getMainGoal
  setGoals []
  sizeGoal g

end ZInQ.Size.Tac

namespace ZInQ.Size.Tac

open Lean Elab Tactic Meta

/-- Prove `Maj B (h + 1) P` (with `2^20 ≤ B` and `1 ≤ B` in the context): find the levels of
`P` by `size`, then check `e ≤ 8h` and `s ≤ 160` by `decide`. -/
elab "size_maj" : tactic => do
  let g ← getMainGoal
  setGoals []
  let gs ← g.apply (← mkConstWithFreshMVarLevels ``maj_of_sz)
  let mut rest := #[]
  for g' in gs do
    let ty ← instantiateMVars (← g'.getType)
    if isStructural ty.cleanupAnnotations then
      sizeGoal g'
    else
      rest := rest.push g'
  for g' in rest do
    unless ← g'.isAssigned do
      if (← isProp (← g'.getType)) then
        sideGoal g'

end ZInQ.Size.Tac
