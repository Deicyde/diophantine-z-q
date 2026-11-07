import ZInQKernel.Compiler.NodeCheck.Builder
import ZInQKernel.Compiler.Circuits.Packed.Construction

/-!
# The fast packed-history construction

The fast transcription of `Packed.construction` (items 1–7) and its `Sim` lemma, and the node
list of the compiled circuit `𝒞_{p,k}` as the reversed node list of the fast run
(`compiled_nodes`).
-/

namespace ZInQ.Compiler.NodeCheck

open Natural RM

/-! ### List helpers -/

theorem getD_map_node (S : List Ex) (i : ℕ) (z : Ex) :
    (S.getD i z).node = (S.map Ex.node).getD i z.node := by
  induction S generalizing i with
  | nil => rfl
  | cons x S ih => cases i <;> simp [ih]

theorem forall₂_append {α β : Type} {R : α → β → Prop} {l₁ l₂ : List α} {l₁' l₂' : List β}
    (h₁ : List.Forall₂ R l₁ l₁') (h₂ : List.Forall₂ R l₂ l₂') :
    List.Forall₂ R (l₁ ++ l₂) (l₁' ++ l₂') := by
  induction h₁ with
  | nil => exact h₂
  | cons h _ ih => exact .cons h ih

theorem forall₂_map {α β γ δ : Type} {R : α → β → Prop} {l : List γ} {f : γ → α} {g : δ → β}
    {e : γ → δ} (h : ∀ x, R (f x) (g (e x))) : List.Forall₂ R (l.map f) ((l.map e).map g) := by
  induction l with
  | nil => exact .nil
  | cons x l ih => exact .cons (h x) ih

theorem forall₂_map' {α β γ : Type} {R : α → β → Prop} {l : List γ} {f : γ → α} {g : γ → β}
    (h : ∀ x, R (f x) (g x)) : List.Forall₂ R (l.map f) (l.map g) := by
  induction l with
  | nil => exact .nil
  | cons x l ih => exact .cons (h x) ih

/-- The erasure of a branch history. -/
def eraseVW (e : ℕ × Ex × Ex) : ℕ × ℕ × ℕ := (e.1, e.2.1.node, e.2.2.node)

/-! ### The fast construction -/

/-- `n` fresh variables, in order. -/
def freshN : ℕ → FM (List ℕ)
  | 0 => pure []
  | n + 1 => do
    let h ← fresh
    let hs ← freshN n
    pure (h :: hs)

theorem freshN_sim (n : ℕ) : Sim (List.map Ex.node) (Packed.freshN n) (freshN n) := by
  induction n with
  | zero => exact Sim.pure rfl
  | succ n ih => exact Sim.bind fresh_sim fun h => Sim.bind ih fun hs => Sim.pure rfl

/-- Concatenate the formula lists of constructions run in order. -/
def seqConcat : List (FM (List FForm)) → FM (List FForm)
  | [] => pure []
  | m :: ms => do
    let a ← m
    let b ← seqConcat ms
    pure (a ++ b)

theorem seqConcat_sim : ∀ {ms : List (NM (List NForm))} {ms' : List (FM (List FForm))},
    List.Forall₂ (Sim (List.map eraseF)) ms ms' →
      Sim (List.map eraseF) (Packed.seqConcat ms) (seqConcat ms')
  | [], [], .nil => Sim.pure rfl
  | _ :: _, _ :: _, .cons h hs =>
    Sim.bind h fun _ => Sim.bind (seqConcat_sim hs) fun _ => Sim.pure (List.map_append ..)

theorem seqM_sim' {ms : List (NM NForm)} {ms' : List (FM FForm)}
    (h : List.Forall₂ (Sim eraseF) ms ms') :
    Sim (List.map eraseF) (Natural.seqM ms) (seqM ms') := seqM_sim h

/-- Item 4 for one register. -/
def registerMasks (K D T F Rj Nj : ℕ) : FM (List FForm) :=
  seqM [
    mask Rj D,
    lt Rj T,
    do bitAnd (← mulL [K, Nj]) (← addL [Rj, D]) (← mulL [K, F])]

theorem registerMasks_sim (K D T F Rj Nj : Ex) :
    Sim (List.map eraseF) (Packed.registerMasks K D T F Rj Nj)
      (registerMasks K.node D.node T.node F.node Rj.node Nj.node) := by
  unfold Packed.registerMasks registerMasks
  apply seqM_sim'
  sim_tac

/-- Item 5. -/
def subBranches (zero : ℕ) (S N : List ℕ) :
    ℕ → List Instr → FM (List FForm × List (ℕ × ℕ × ℕ))
  | _, [] => pure ([], [])
  | i, .dec j _ _ :: rest => do
    let V ← fresh
    let W ← fresh
    let fs ← seqM [
      bitAnd V (S.getD i zero) (N.getD j zero),
      do pure (.eq (S.getD i zero) (← addL [V, W]))]
    let rest' ← subBranches zero S N (i + 1) rest
    pure (fs ++ rest'.1, (i, V, W) :: rest'.2)
  | i, _ :: rest => subBranches zero S N (i + 1) rest

theorem subBranches_sim (zero : Ex) (S N : List Ex) (i : ℕ) (p : List Instr) :
    Sim (fun r => (r.1.map eraseF, r.2.map eraseVW)) (Packed.subBranches zero S N i p)
      (subBranches zero.node (S.map Ex.node) (N.map Ex.node) i p) := by
  induction p generalizing i with
  | nil => exact Sim.pure rfl
  | cons ins rest ih =>
    cases ins with
    | inc j x => exact ih (i + 1)
    | halt => exact ih (i + 1)
    | dec j x y =>
      unfold Packed.subBranches subBranches
      refine Sim.bind fresh_sim fun V => Sim.bind fresh_sim fun W => Sim.bind (seqM_sim' ?_)
        fun fs => Sim.bind (ih (i + 1)) fun rest' => Sim.pure (by simp [eraseVW])
      refine .cons (bitAnd_sim rfl (getD_map_node ..) (getD_map_node ..)) (.cons ?_ .nil)
      exact Sim.bind (addL_sim rfl) fun e => Sim.pure (by simp [eraseF, getD_map_node])

/-- The branch histories of instruction `i`. -/
def lookupVW (zero : ℕ) (vw : List (ℕ × ℕ × ℕ)) (i : ℕ) : ℕ × ℕ :=
  ((vw.find? fun e => e.1 == i).map (·.2)).getD (zero, zero)

theorem lookupVW_erase (zero : Ex) (vw : List (ℕ × Ex × Ex)) (i : ℕ) :
    ((Packed.lookupVW zero vw i).1.node, (Packed.lookupVW zero vw i).2.node) =
      lookupVW zero.node (vw.map eraseVW) i := by
  unfold Packed.lookupVW lookupVW
  rw [List.find?_map]
  have : ((fun e : ℕ × ℕ × ℕ => e.1 == i) ∘ eraseVW) = fun e => e.1 == i := rfl
  rw [this]
  cases vw.find? (fun e => e.1 == i) with
  | none => rfl
  | some e => rfl

/-- The summands of `A_j`. -/
def incHandles (p : Program) (zero : ℕ) (S : List ℕ) (j : ℕ) : List ℕ :=
  ((List.range p.length).filter fun i => decide (Packed.incOn p j i)).map fun i => S.getD i zero

/-- The summands of `C_j`. -/
def decHandles (p : Program) (zero : ℕ) (vw : List (ℕ × ℕ × ℕ)) (j : ℕ) : List ℕ :=
  ((List.range p.length).filter fun i => decide (Packed.decOn p j i)).map fun i =>
    (lookupVW zero vw i).1

/-- The summands of `I_i`. -/
def inHandles (p : Program) (zero : ℕ) (S : List ℕ) (vw : List (ℕ × ℕ × ℕ)) (i : ℕ) :
    List ℕ :=
  (List.range p.length).flatMap fun i' =>
    (if Packed.incTo p i' i then [S.getD i' zero] else []) ++
      (if Packed.nzTo p i' i then [(lookupVW zero vw i').1] else []) ++
      (if Packed.zTo p i' i then [(lookupVW zero vw i').2] else [])

theorem incHandles_erase (p : Program) (zero : Ex) (S : List Ex) (j : ℕ) :
    (Packed.incHandles p zero S j).map Ex.node = incHandles p zero.node (S.map Ex.node) j := by
  simp [Packed.incHandles, incHandles, List.map_map, Function.comp_def, getD_map_node]

theorem decHandles_erase (p : Program) (zero : Ex) (vw : List (ℕ × Ex × Ex)) (j : ℕ) :
    (Packed.decHandles p zero vw j).map Ex.node =
      decHandles p zero.node (vw.map eraseVW) j := by
  simp only [Packed.decHandles, decHandles, List.map_map, Function.comp_def]
  congr 1
  funext i
  exact congrArg Prod.fst (lookupVW_erase zero vw i)

theorem inHandles_erase (p : Program) (zero : Ex) (S : List Ex) (vw : List (ℕ × Ex × Ex))
    (i : ℕ) :
    (Packed.inHandles p zero S vw i).map Ex.node =
      inHandles p zero.node (S.map Ex.node) (vw.map eraseVW) i := by
  simp only [Packed.inHandles, inHandles, List.map_flatMap]
  congr 1
  funext i'
  have h1 := congrArg Prod.fst (lookupVW_erase zero vw i')
  have h2 := congrArg Prod.snd (lookupVW_erase zero vw i')
  simp only at h1 h2
  split_ifs <;> simp [h1, h2, getD_map_node]

/-- Item 6 for one register. -/
def registerEq (B Rj ιj : ℕ) (decs incs : List ℕ) : FM FForm := do
  let l ← addL [Rj, ← mulL [B, ← addL decs]]
  let r ← addL [ιj, ← mulL [B, Rj], ← mulL [B, ← addL incs]]
  pure (.eq l r)

theorem registerEq_sim {B Rj ιj : Ex} {decs incs : List Ex} {decs' incs' : List ℕ}
    (hd : decs.map Ex.node = decs') (hi : incs.map Ex.node = incs') :
    Sim eraseF (Packed.registerEq B Rj ιj decs incs)
      (registerEq B.node Rj.node ιj.node decs' incs') := by
  unfold Packed.registerEq registerEq
  sim_tac
  all_goals assumption

/-- Item 7 for one state. -/
def stateEq (B Si e : ℕ) (ins : List ℕ) : FM FForm := do
  let r ← addL [e, ← mulL [B, ← addL ins]]
  pure (.eq Si r)

theorem stateEq_sim {B Si e : Ex} {ins : List Ex} {ins' : List ℕ}
    (hi : ins.map Ex.node = ins') :
    Sim eraseF (Packed.stateEq B Si e ins) (stateEq B.node Si.node e.node ins') := by
  unfold Packed.stateEq stateEq
  sim_tac
  all_goals assumption

/-- Run two formula-list constructions in order and concatenate their formulas. -/
def appendM (m₁ m₂ : FM (List FForm)) : FM (List FForm) := do
  let l₁ ← m₁
  let l₂ ← m₂
  pure (l₁ ++ l₂)

theorem appendM_sim {m₁ m₂ : NM (List NForm)} {m₁' m₂' : FM (List FForm)}
    (h₁ : Sim (List.map eraseF) m₁ m₁') (h₂ : Sim (List.map eraseF) m₂ m₂') :
    Sim (List.map eraseF) (Packed.appendM m₁ m₂) (appendM m₁' m₂') :=
  Sim.bind h₁ fun _ => Sim.bind h₂ fun _ => Sim.pure (List.map_append ..)

/-- Item 1. -/
def items1 (p : Program) (a : List ℕ) (zero q c K B T : ℕ) : FM (List FForm) :=
  seqM ([
    lt zero c,
    do power K (← constant 2) c,
    do pure (.eq B (← scale 4 K)),
    do lt (← constant p.length) B,
    power T B q] ++ a.map fun ai => lt ai K)

theorem items1_sim (p : Program) (a : List Ex) (zero q c K B T : Ex) :
    Sim (List.map eraseF) (Packed.items1 p a zero q c K B T)
      (items1 p (a.map Ex.node) zero.node q.node c.node K.node B.node T.node) := by
  unfold Packed.items1 items1
  refine seqM_sim' (forall₂_append ?_ (forall₂_map fun ai => lt_sim rfl rfl))
  sim_tac

/-- Item 2. -/
def items2 (zero one K B T F D : ℕ) (S : List ℕ) : FM (List FForm) :=
  seqM [
    do pure (.eq (← addL [← mulL [B, F], one]) (← addL [F, ← mulL [B, T]])),
    do pure (.eq (← addL [D, F]) (← mulL [K, F])),
    do pure (.eq (← addL S) F),
    pure (.eq (S.getLastD zero) T)]

theorem getLastD_map_node (S : List Ex) (z : Ex) :
    (S.getLastD z).node = (S.map Ex.node).getLastD z.node := by
  simp only [List.getLastD_eq_getLast?, List.getLast?_map]
  cases S.getLast? <;> rfl

theorem items2_sim (zero one K B T F D : Ex) (S : List Ex) :
    Sim (List.map eraseF) (Packed.items2 zero one K B T F D S)
      (items2 zero.node one.node K.node B.node T.node F.node D.node (S.map Ex.node)) := by
  unfold Packed.items2 items2
  apply seqM_sim'
  sim_tac
  simp [eraseF, getLastD_map_node]

/-- Item 3. -/
def items3 (F : ℕ) (S : List ℕ) : FM (List FForm) := seqM (S.map fun x => mask x F)

theorem items3_sim (F : Ex) (S : List Ex) :
    Sim (List.map eraseF) (Packed.items3 F S) (items3 F.node (S.map Ex.node)) :=
  seqM_sim' (forall₂_map fun _ => mask_sim rfl rfl)

/-- Item 4. -/
def items4 (r : ℕ) (zero K D T F : ℕ) (R N : List ℕ) : FM (List FForm) :=
  seqConcat ((List.range r).map fun j =>
    registerMasks K D T F (R.getD j zero) (N.getD j zero))

theorem items4_sim (r : ℕ) (zero K D T F : Ex) (R N : List Ex) :
    Sim (List.map eraseF) (Packed.items4 r zero K D T F R N)
      (items4 r zero.node K.node D.node T.node F.node (R.map Ex.node) (N.map Ex.node)) := by
  unfold Packed.items4 items4
  apply seqConcat_sim
  refine forall₂_map' fun j => ?_
  simp only [id, ← getD_map_node]
  exact registerMasks_sim ..

/-- Item 6. -/
def items6 (p : Program) (r : ℕ) (a : List ℕ) (zero B : ℕ) (R S : List ℕ)
    (vw : List (ℕ × ℕ × ℕ)) : FM (List FForm) :=
  seqM ((List.range r).map fun j =>
    registerEq B (R.getD j zero) (a.getD j zero) (decHandles p zero vw j)
      (incHandles p zero S j))

theorem items6_sim (p : Program) (r : ℕ) (a : List Ex) (zero B : Ex) (R S : List Ex)
    (vw : List (ℕ × Ex × Ex)) :
    Sim (List.map eraseF) (Packed.items6 p r a zero B R S vw)
      (items6 p r (a.map Ex.node) zero.node B.node (R.map Ex.node) (S.map Ex.node)
        (vw.map eraseVW)) := by
  unfold Packed.items6 items6
  apply seqM_sim'
  refine forall₂_map' fun j => ?_
  simp only [id, ← getD_map_node]
  exact registerEq_sim (decHandles_erase ..) (incHandles_erase ..)

/-- Item 7. -/
def items7 (p : Program) (zero one B : ℕ) (S : List ℕ) (vw : List (ℕ × ℕ × ℕ)) :
    FM (List FForm) :=
  seqM ((List.range p.length).map fun i =>
    stateEq B (S.getD i zero) (if i = 0 then one else zero) (inHandles p zero S vw i))

theorem items7_sim (p : Program) (zero one B : Ex) (S : List Ex) (vw : List (ℕ × Ex × Ex)) :
    Sim (List.map eraseF) (Packed.items7 p zero one B S vw)
      (items7 p zero.node one.node B.node (S.map Ex.node) (vw.map eraseVW)) := by
  unfold Packed.items7 items7
  apply seqM_sim'
  refine forall₂_map' fun i => ?_
  simp only [id, ← getD_map_node]
  have h : (if i = 0 then one else zero).node = if i = 0 then one.node else zero.node := by
    split_ifs <;> rfl
  rw [← h]
  exact stateEq_sim (inHandles_erase ..)

/-- Items 1–7. -/
def packedFormulas (p : Program) (r : ℕ) (a : List ℕ) (zero one q c K B T F D : ℕ)
    (R N S : List ℕ) : FM (List FForm) :=
  appendM (items1 p a zero q c K B T) <|
  appendM (items2 zero one K B T F D S) <|
  appendM (items3 F S) <|
  appendM (items4 r zero K D T F R N) do
    let sb ← subBranches zero S N 0 p
    appendM (pure sb.1) <|
    appendM (items6 p r a zero B R S sb.2) (items7 p zero one B S sb.2)

theorem packedFormulas_sim (p : Program) (r : ℕ) (a : List Ex) (zero one q c K B T F D : Ex)
    (R N S : List Ex) :
    Sim (List.map eraseF) (Packed.packedFormulas p r a zero one q c K B T F D R N S)
      (packedFormulas p r (a.map Ex.node) zero.node one.node q.node c.node K.node B.node
        T.node F.node D.node (R.map Ex.node) (N.map Ex.node) (S.map Ex.node)) := by
  unfold Packed.packedFormulas packedFormulas
  refine appendM_sim (items1_sim ..) (appendM_sim (items2_sim ..) (appendM_sim (items3_sim ..)
    (appendM_sim (items4_sim ..) (Sim.bind (subBranches_sim ..) fun sb => ?_))))
  exact appendM_sim (Sim.pure rfl) (appendM_sim (items6_sim ..) (items7_sim ..))

/-- The fast packed-history construction. -/
def construction (p : Program) (r k : ℕ) : FM FForm := do
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
  let φs ← packedFormulas p r a zero one q c K B T F D R N S
  pure (.and φs)

theorem inputs_map_node (k : ℕ) : (inputs k).map Ex.node = List.range k := by
  simp [inputs, List.map_map, Function.comp_def]

theorem construction_sim (p : Program) (r k : ℕ) :
    Sim eraseF (Packed.construction p r k) (construction p r k) := by
  unfold Packed.construction construction
  refine Sim.bind (constant_sim 0) fun zero => Sim.bind (constant_sim 1) fun one =>
    Sim.bind fresh_sim fun q => Sim.bind fresh_sim fun c => Sim.bind fresh_sim fun K =>
    Sim.bind fresh_sim fun B => Sim.bind fresh_sim fun T => Sim.bind fresh_sim fun F =>
    Sim.bind fresh_sim fun D => Sim.bind (freshN_sim r) fun R => Sim.bind (freshN_sim r) fun N =>
    Sim.bind (freshN_sim p.length) fun S => ?_
  rw [← inputs_map_node]
  exact Sim.bind (packedFormulas_sim ..) fun φs => Sim.pure (by simp [eraseF, eraseFs_eq])

/-! ### The compiled circuit -/

/-- The initial fast state with `k` inputs. -/
def FState.init (k : ℕ) : FState := ⟨k, Table.empty, k, ((List.range k).map .var).reverse⟩

theorem rel_init (k : ℕ) : Rel (State.init k) (FState.init k) := by
  refine ⟨rfl, by simp [State.init, FState.init], by simp [FState.init], ?_, ?_, ?_⟩
  · intro n hn
    show Table.empty.find n = _
    rw [Table.find_empty, eq_comm, List.idxOf?_eq_none_iff]
    intro h
    simp only [State.init, List.mem_map, List.mem_range] at h
    obtain ⟨i, -, rfl⟩ := h
    simp [tabled] at hn
  · intro i hi
    simpa [State.init] using hi
  · simp [State.init, List.countP_map, Function.comp_def, isVarNode]

/-- The reversed node list of the fast run of the packed-history construction, with the
encoding of its formula. -/
def fastNodesRev (p : Program) (r k : ℕ) : List NatNode :=
  match construction p r k (FState.init k) with
  | (φ, t) => (φ.encode t).2.rev

/-- **The node list of the compiled circuit** is the reversed node list of the fast run. -/
theorem compiled_nodes (p : Program) (r k : ℕ) :
    (Packed.compiled p r k).nodes = (fastNodesRev p r k).reverse := by
  have h1 := (construction_sim p r k).run _ _ (rel_init k)
  have h2 := (encode_sim Syntax.ExPoly.empty
    (Packed.construction p r k (State.init k)).1).run _ _ h1.2
  rw [h1.1] at h2
  rw [Packed.compiled, NM.toCircuit_nodes, h2.2.nodes, fastNodesRev]

/-- The variable nodes of the compiled circuit are as many as its explicit variables. -/
theorem compiled_varNodes (p : Program) (r k : ℕ) :
    (Packed.compiled p r k).nodes.countP isVarNode = (Packed.compiled p r k).explicitVars.length := by
  have h1 := (construction_sim p r k).run _ _ (rel_init k)
  have h2 := (encode_sim Syntax.ExPoly.empty
    (Packed.construction p r k (State.init k)).1).run _ _ h1.2
  rw [Packed.compiled, NM.toCircuit_nodes, NM.toCircuit_explicitVars]
  exact h2.2.vars

end ZInQ.Compiler.NodeCheck
