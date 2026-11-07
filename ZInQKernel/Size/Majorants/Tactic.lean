import ZInQKernel.Size.Majorants.Calculus

/-!
# The tactic `size`

`size` proves a goal `Scale B ?e ?s P` (or `PScale`, `AScale`, `FAll`) whose levels are metavariables:
it applies the rules of `ZInQKernel.Size.Majorants.Calculus` by the head symbol of the
subject, from the root to the leaves, and the leaves fix the levels. The levels it produces
are closed expressions built from numerals, `max`, `+` and `*`, compared with the target by
`decide` afterwards.

The tactic unfolds the definitions of formulas, pairs and codes it does not know, uses the
hypotheses of the context for callees and constructors (`Scale B e s τ.poly`,
`∀ c, Scale B e s (I.psi n c)`, …), and closes numeric side conditions (bounds on constants and
exponents, list lengths) by `decide`. It never unfolds the polynomial of a template.
-/

namespace ZInQ.Size.Tac

open MvPolynomial ZInQ.Syntax

/-! ### Rules with their numeric parameter first -/

theorem C (k : ℕ) {B : ℕ} {σ : Type*} (hB : 1 ≤ B) {c : ℤ} (hc : c.natAbs ≤ 2 ^ 2 ^ k) :
    Scale B 0 k (MvPolynomial.C c : MvPolynomial σ ℤ) := Scale.C hB hc

theorem intCast (k : ℕ) {B : ℕ} {σ : Type*} (hB : 1 ≤ B) {c : ℤ} (hc : c.natAbs ≤ 2 ^ 2 ^ k) :
    Scale B 0 k (c : MvPolynomial σ ℤ) := Scale.intCast hB hc

theorem ofNat (k : ℕ) {B : ℕ} {σ : Type*} (hB : 1 ≤ B) (n : ℕ) [n.AtLeastTwo]
    (hn : n ≤ 2 ^ 2 ^ k) : Scale B 0 k (OfNat.ofNat n : MvPolynomial σ ℤ) := Scale.ofNat hB n hn

theorem pow (k : ℕ) {B e s : ℕ} {σ : Type*} {P : MvPolynomial σ ℤ} {n : ℕ} (hP : Scale B e s P)
    (hn : n ≤ 2 ^ k) : Scale B e (s + k) (P ^ n) := hP.pow hn

theorem ppow (m : ℕ) {B e s : ℕ} (hB : 1 ≤ B) {u : Pair} {n : ℕ} (hn : n < 2 ^ m)
    (hu : PScale B e s u) : PScale B e (s + 3 * m) (u.pow n) := PScale.pow hB m hn hu

theorem ofInt (k : ℕ) {B : ℕ} (hB : 1 ≤ B) {a b : ℤ} (ha : a.natAbs ≤ 2 ^ 2 ^ k)
    (hb : b.natAbs ≤ 2 ^ 2 ^ k) : PScale B 0 k (Pair.ofInt a b) := PScale.ofInt' hB k ha hb

theorem and (k : ℕ) {B e s : ℕ} (hB : 1 ≤ B) {fs : List Formula} (hfs : FAll B e s fs)
    (hlen : fs.length ≤ 2 ^ k) : Scale B e (s + 1 + k) (Formula.and fs).compile :=
  Scale.compile_and' hB k hfs hlen

theorem or (k : ℕ) {B e s : ℕ} {fs : List Formula} (hfs : FAll B e s fs)
    (hlen : fs.length ≤ 2 ^ k) : Scale B e (s + k) (Formula.or fs).compile :=
  Scale.compile_or' k hfs hlen

theorem ofFn {B e s n : ℕ} {f : Fin n → Formula} (h : ∀ i, Scale B e s (f i).compile) :
    FAll B e s (List.ofFn f) := by
  intro φ hφ
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hφ
  exact h i

theorem pairs {B e s n : ℕ} {D : Fin n → Pair} (h : ∀ i, PScale B e s (D i)) :
    AScale B e s (pairsArgs D) := by
  intro k
  unfold pairsArgs
  split_ifs
  exacts [(h _).1, (h _).2]

/-! ### The tactic -/

open Lean Elab Tactic Meta

/-- Close a side condition: by assumption (`1 ≤ B`), by evaluation of `Nat.ble`, by
`decide` or by `simp`. -/
def sideGoal (g : MVarId) : TacticM Unit := g.withContext do
  if (← observing? (withReducible g.assumption)).isSome then return
  let saved ← getGoals
  let attempts : List (TSyntax `tactic) :=
    [← `(tactic| exact Nat.le_of_ble_eq_true rfl), ← `(tactic| decide), ← `(tactic| simp)]
  for tac in attempts do
    let s ← saveState
    try
      setGoals [g]
      withoutRecover (evalTactic tac)
      let pf ← instantiateMVars (mkMVar g)
      if (← getGoals).isEmpty && !pf.hasSyntheticSorry && !pf.hasExprMVar then
        setGoals saved
        return
      s.restore
    catch _ => s.restore
  setGoals saved
  throwError "size: cannot prove the side condition{indentExpr (← g.getType)}"

/-- The smallest `k` with `n ≤ 2^k`. -/
def ceilLog2 (n : ℕ) : ℕ := Id.run do
  let mut k := 0
  while 2 ^ k < n do
    k := k + 1
  return k

def isStructural (tgt : Expr) : Bool :=
  let fn := tgt.getAppFn
  fn.isConstOf ``Scale || fn.isConstOf ``PScale || fn.isConstOf ``AScale || fn.isConstOf ``FAll

/-- The recursion depth allowed to `size`: far beyond the depth of any subject it meets. -/
def sizeFuel : ℕ := 100000

mutual

/-- Apply the lemma `e` to `g`, close the side conditions, then solve the structural goals. -/
def applyThen : ℕ → MVarId → Expr → TacticM Unit
  | 0, _, _ => throwError "size: recursion limit reached"
  | fuel + 1, g, e => do
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
      sizeGoal fuel g'

/-- Try the lemmas in order (with backtracking on failures). -/
def tryLemmas : ℕ → MVarId → List (TacticM Expr) → TacticM Unit
  | 0, _, _ => throwError "size: recursion limit reached"
  | _ + 1, g, [] => do throwError "size: no rule applies to{indentExpr (← g.getType)}"
  | fuel + 1, g, e :: es => do
    let saved ← saveState
    try
      applyThen fuel g (← e)
    catch ex =>
      if es.isEmpty then throw ex
      saved.restore
      tryLemmas fuel g es

/-- Replace the subject (argument `k`) of the goal by its unfolding and retry. -/
def unfoldSubject : ℕ → MVarId → Expr → ℕ → TacticM Unit
  | 0, _, _, _ => throwError "size: recursion limit reached"
  | fuel + 1, g, tgt, k => do
    let fn := tgt.getAppFn
    let args := tgt.getAppArgs
    let e ← whnfCore args[k]!
    if let some e' ← unfoldDefinition? e then
      let g' ← g.replaceTargetDefEq (mkAppN fn (args.set! k e'))
      sizeGoal fuel g'
    else
      throwError "size: cannot handle{indentExpr tgt}"

def sizeGoal : ℕ → MVarId → TacticM Unit
  | 0, _ => throwError "size: recursion limit reached"
  | fuel + 1, g => g.withContext do
    if ← g.isAssigned then return
    let tgt := (← instantiateMVars (← g.getType)).cleanupAnnotations.headBeta
    if tgt.isForall then
      if !(← isProp tgt.bindingDomain!) then
        let (_, g') ← g.intro1
        sizeGoal fuel g'
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
          for g' in gs do sizeGoal fuel g'
          return
        catch _ => saved.restore
    let fn := tgt.getAppFn
    let args := tgt.getAppArgs
    let c (n : Name) : TacticM Expr := mkConstWithFreshMVarLevels n
    let cn (n : Name) (k : ℕ) : TacticM Expr := do return mkApp (← c n) (mkNatLit k)
    if fn.isConstOf ``Scale then
      let P ← whnfCore args[4]!
      let head := P.getAppFn
      match head.constName? with
      | some ``HAdd.hAdd => applyThen fuel g (← c ``Scale.add')
      | some ``HSub.hSub => applyThen fuel g (← c ``Scale.sub')
      | some ``HMul.hMul => applyThen fuel g (← c ``Scale.mul')
      | some ``Neg.neg => applyThen fuel g (← c ``Scale.neg')
      | some ``HPow.hPow =>
        let some n ← (evalNat (P.getArg! 5)).run | throwError "size: exponent is not a numeral{indentExpr P}"
        applyThen fuel g (← cn ``Tac.pow (ceilLog2 n))
      | some ``MvPolynomial.X => applyThen fuel g (← c ``Scale.X')
      | some ``Int.cast => tryLemmas fuel g ([0, 3, 5, 7].map fun k => cn ``Tac.intCast k)
      | some ``OfNat.ofNat =>
        match (P.getArg! 1).rawNatLit? with
        | some 0 => applyThen fuel g (← c ``Scale.zero')
        | some 1 => applyThen fuel g (← c ``Scale.one')
        | _ => tryLemmas fuel g ([0, 3, 5, 7].map fun k => cn ``Tac.ofNat k)
      | some ``Zero.zero => applyThen fuel g (← c ``Scale.zero')
      | some ``One.one => applyThen fuel g (← c ``Scale.one')
      | some ``Formula.compile =>
        let φ ← whnfCore P.appArg!
        match φ.getAppFn.constName? with
        | some ``Formula.eq => applyThen fuel g (← c ``Scale.compile_eq')
        | some ``Formula.atom => applyThen fuel g (← c ``Scale.compile_atom')
        | some ``Formula.call => applyThen fuel g (← c ``Scale.compile_call')
        | some ``Formula.and => tryLemmas fuel g ([1, 2, 3, 4, 5, 6, 7].map fun k => cn ``Tac.and k)
        | some ``Formula.or => tryLemmas fuel g ([1, 2, 3].map fun k => cn ``Tac.or k)
        | _ =>
          if let some φ' ← unfoldDefinition? φ then
            let P' := mkApp P.appFn! φ'
            let g' ← g.replaceTargetDefEq (mkAppN fn (args.set! 4 P'))
            sizeGoal fuel g'
          else throwError "size: cannot handle the formula{indentExpr φ}"
      | some ``ExPoly.call => applyThen fuel g (← c ``Scale.call')
      | some ``Pair.norm => applyThen fuel g (← c ``PScale.norm')
      | some ``Prod.fst => applyThen fuel g (← c ``PScale.fst)
      | some ``Prod.snd => applyThen fuel g (← c ``PScale.snd)
      | some ``DFunLike.coe =>
        if P.getAppNumArgs == 6 && (P.getArg! 4).isAppOf ``MvPolynomial.C then
          tryLemmas fuel g ([0, 3, 5, 7].map fun k => cn ``Tac.C k)
        else if P.getAppNumArgs == 6 && (P.getArg! 4).isAppOf ``MvPolynomial.bind₁ then
          applyThen fuel g (← c ``Scale.bind₁_fin)
        else throwError "size: cannot handle{indentExpr P}"
      | _ =>
        -- an entry `g k` of an argument tuple
        if P.isApp then
          let fType ← whnf (← inferType P.appFn!)
          if fType.isForall && fType.bindingDomain!.isAppOf ``Fin then
            applyThen fuel g (← c ``Scale.app)
            return
        unfoldSubject fuel g tgt 4
    else if fn.isConstOf ``PScale then
      let u ← whnfCore args[3]!
      match u.getAppFn.constName? with
      | some ``Pair.mul => applyThen fuel g (← c ``PScale.mul')
      | some ``Pair.sq => applyThen fuel g (← c ``PScale.sq')
      | some ``Pair.add => applyThen fuel g (← c ``PScale.add')
      | some ``Pair.sub => applyThen fuel g (← c ``PScale.sub')
      | some ``Pair.neg => applyThen fuel g (← c ``PScale.neg')
      | some ``Pair.smul => applyThen fuel g (← c ``PScale.smul')
      | some ``Pair.conj => applyThen fuel g (← c ``PScale.conj')
      | some ``Pair.pow =>
        let some n ← (evalNat u.appArg!).run | throwError "size: exponent is not a numeral{indentExpr u}"
        applyThen fuel g (← cn ``Tac.ppow (ceilLog2 (n + 1)))
      | some ``Pair.ofInt => tryLemmas fuel g ([0, 3, 5, 7].map fun k => cn ``Tac.ofInt k)
      | some ``Prod.mk => applyThen fuel g (← c ``PScale.mk')
      | some ``varPair => applyThen fuel g (← c ``PScale.varPair)
      | some ``Code.x => applyThen fuel g (← c ``PScale.x)
      | some ``Code.y => applyThen fuel g (← c ``PScale.y)
      | some ``slopeW => applyThen fuel g (← c ``PScale.slopeW')
      | some ``Pair.log25 => applyThen fuel g (← c ``PScale.log25')
      | _ => unfoldSubject fuel g tgt 3
    else if fn.isConstOf ``AScale then
      let a ← whnfCore args[4]!
      match a.getAppFn.constName? with
      | some ``Fin.append => applyThen fuel g (← c ``AScale.append')
      | some ``Matrix.vecCons => applyThen fuel g (← c ``AScale.cons')
      | some ``Matrix.vecEmpty => applyThen fuel g (← c ``AScale.nil)
      | some ``varPoint => applyThen fuel g (← c ``AScale.varPoint)
      | some ``varArgs => applyThen fuel g (← c ``AScale.varArgs)
      | some ``Code.neg => applyThen fuel g (← c ``AScale.neg)
      | some ``Code.O => applyThen fuel g (← c ``AScale.O)
      | some ``Pair.args => applyThen fuel g (← c ``PScale.args)
      | some ``codesArgs => applyThen fuel g (← c ``AScale.codes)
      | some ``pairsArgs => applyThen fuel g (← c ``Tac.pairs)
      | _ =>
        if a.isLambda then
          let (_, g') ← g.intro1
          sizeGoal fuel g'
        else unfoldSubject fuel g tgt 4
    else
      -- `FAll`
      let l ← whnfR args[3]!
      match l.getAppFn.constName? with
      | some ``List.cons => applyThen fuel g (← c ``FAll.cons')
      | some ``List.nil => applyThen fuel g (← c ``FAll.nil)
      | some ``HAppend.hAppend => applyThen fuel g (← c ``FAll.append')
      | some ``List.ofFn => applyThen fuel g (← c ``Tac.ofFn)
      | _ => unfoldSubject fuel g tgt 3

end

/-- Prove a size goal `Scale B ?e ?s P` (or `PScale`, `AScale`, `FAll`) with metavariable levels. -/
elab "size" : tactic => do
  let g ← getMainGoal
  setGoals []
  sizeGoal sizeFuel g

end ZInQ.Size.Tac

namespace ZInQ.Size.Tac

open Lean Elab Tactic Meta

/-- Apply `lem`, prove its structural premises by `size` and its numeric premises by
`decide`. -/
def sizeVia (lem : Name) : TacticM Unit := do
  let g ← getMainGoal
  setGoals []
  let gs ← g.apply (← mkConstWithFreshMVarLevels lem)
  let mut rest := #[]
  for g' in gs do
    let ty ← instantiateMVars (← g'.getType)
    if isStructural ty.cleanupAnnotations then
      sizeGoal sizeFuel g'
    else
      rest := rest.push g'
  for g' in rest do
    unless ← g'.isAssigned do
      if (← isProp (← g'.getType)) then
        sideGoal g'

theorem mono_to {σ : Type*} {B e s e' s' : ℕ} {P : MvPolynomial σ ℤ} (hB : 1 ≤ B)
    (h : Scale B e s P) (he : e ≤ e') (hs : s ≤ s') : Scale B e' s' P := h.mono hB he hs

/-- Prove `Maj B (h + 1) P` (with `2^20 ≤ B` and `1 ≤ B` in the context): find the levels of
`P` by `size`, then check `e ≤ 8h` and `s ≤ 160` by `decide`. -/
elab "size_maj" : tactic => sizeVia ``maj_of_sz

/-- Prove `Scale B e s P` for given numerals `e`, `s` (with `1 ≤ B` in the context). -/
elab "size_le" : tactic => sizeVia ``mono_to

end ZInQ.Size.Tac
