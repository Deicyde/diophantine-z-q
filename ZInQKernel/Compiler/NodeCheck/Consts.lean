import ZInQKernel.Compiler.Universal.NodeCheck

/-!
# The constants of the halting circuit, symbolically

`CTo S m T`: run from any state whose constant list (`constList` of its node list) is `S`, the
construction `m` ends with constant list `T`. A constant request `constant c` maps `S` to
`addC c S` (append `c` unless present); every other builder operation keeps the constant
list. The gadgets and macros request only `0, 1, 2`; item 1 of the packed construction requests
`2, 4` and the program length; the node encoding requests `-1` (once a formula has an
equation atom). Hence the constant list of `ℋ` is `0, 1, 2, 4, 1399, -1`, without evaluating the
construction (`haltingCircuit_constList`).
-/

namespace ZInQ.Compiler.NodeCheck

open Natural Packed RM Universal

/-- Append `c` unless present. -/
def addC (c : ℤ) (S : List ℤ) : List ℤ := if c ∈ S then S else S ++ [c]

theorem addC_of_mem {c : ℤ} {S : List ℤ} (h : c ∈ S) : addC c S = S := by simp [addC, h]

theorem mem_addC_of_mem {c d : ℤ} {S : List ℤ} (h : d ∈ S) : d ∈ addC c S := by
  unfold addC; split_ifs <;> simp [h]

theorem addC_idem (c : ℤ) (S : List ℤ) : addC c (addC c S) = addC c S := by
  unfold addC; split_ifs with h h' <;> simp_all

/-- From constant list `S`, `m` ends with constant list `T`. -/
structure CTo {α : Type} (S : List ℤ) (m : NM α) (T : List ℤ) : Prop where
  run : ∀ s : State, constList s.nodes = S → constList (m s).2.nodes = T

namespace CTo

variable {α β : Type}

theorem pure (S : List ℤ) (a : α) : CTo S (Pure.pure a : NM α) S := ⟨fun _ h => h⟩

theorem bind {S T U : List ℤ} {m : NM α} {f : α → NM β} (hm : CTo S m T)
    (hf : ∀ a, CTo T (f a) U) : CTo S (m >>= f) U := ⟨fun s h => (hf _).run _ (hm.run s h)⟩

theorem bind_eq {S T U V : List ℤ} {m : NM α} {f : α → NM β} (hf : ∀ a, CTo T (f a) U)
    (hm : CTo S m T) (hV : U = V) : CTo S (m >>= f) V := hV ▸ bind hm hf

theorem congr {S T T' : List ℤ} {m : NM α} (h : CTo S m T) (hT : T = T') : CTo S m T' := hT ▸ h

theorem constList_append_nonconst (l : List NatNode) {n : NatNode} (hn : constOf n = none) :
    constList (l ++ [n]) = constList l := by
  simp [constList, List.filterMap_append, hn]

theorem const_mem_iff (l : List NatNode) (c : ℤ) : NatNode.const c ∈ l ↔ c ∈ constList l := by
  simp only [constList, List.mem_filterMap]
  constructor
  · intro h; exact ⟨_, h, rfl⟩
  · rintro ⟨n, hn, hc⟩
    cases n <;> simp_all [constOf]

theorem node_nonconst (S : List ℤ) {n : NatNode} (hn : constOf n = none) :
    CTo S (Natural.node n) S := ⟨fun s h => by
  unfold Natural.node
  split
  · exact h
  · rw [constList_append_nonconst _ hn]; exact h⟩

theorem constant (S : List ℤ) (c : ℤ) : CTo S (Natural.constant c) (addC c S) := ⟨fun s h => by
  show constList (Natural.node (.const c) s).2.nodes = _
  unfold Natural.node addC
  split
  · rename_i j hj
    have : NatNode.const c ∈ s.nodes := List.isSome_idxOf?.mp (by rw [hj]; rfl)
    rw [const_mem_iff, h] at this
    rw [ite_cond_eq_true _ _ (eq_true this)]; exact h
  · rename_i hj
    have : NatNode.const c ∉ s.nodes := List.idxOf?_eq_none_iff.mp hj
    rw [const_mem_iff, h] at this
    rw [ite_cond_eq_false _ _ (eq_false this)]
    simp [constList, List.filterMap_append, constOf, ← h]⟩

theorem constant_of_mem {S : List ℤ} {c : ℤ} (hc : c ∈ S) : CTo S (Natural.constant c) S :=
  (constant S c).congr (addC_of_mem hc)

theorem note (S : List ℤ) (k : MacroKind) : CTo S (Natural.note k) S := ⟨fun _ h => h⟩

theorem fresh (S : List ℤ) : CTo S Natural.fresh S := ⟨fun s h => by
  show constList (Natural.node (.var s.next) _).2.nodes = S
  exact (node_nonconst S rfl).run _ h⟩

theorem callPower (S : List ℤ) (P Q R : Ex) : CTo S (Natural.callPower P Q R) S :=
  ⟨fun s h => by
    simp only [Natural.callPower]
    rw [constList_append_nonconst _ rfl]; exact h⟩

theorem addFrom (S : List ℤ) (acc : Ex) (ys : List Ex) : CTo S (Natural.addFrom acc ys) S := by
  induction ys generalizing acc with
  | nil => exact pure S acc
  | cons y ys ih => exact bind (node_nonconst S rfl) fun i => ih _

theorem mulFrom (S : List ℤ) (acc : Ex) (ys : List Ex) : CTo S (Natural.mulFrom acc ys) S := by
  induction ys generalizing acc with
  | nil => exact pure S acc
  | cons y ys ih => exact bind (node_nonconst S rfl) fun i => ih _

theorem addL {S : List ℤ} (h0 : (0 : ℤ) ∈ S) (xs : List Ex) : CTo S (Natural.addL xs) S := by
  cases xs with
  | nil => exact constant_of_mem h0
  | cons x xs => exact addFrom S x xs

theorem mulL {S : List ℤ} (h1 : (1 : ℤ) ∈ S) (xs : List Ex) : CTo S (Natural.mulL xs) S := by
  cases xs with
  | nil => exact constant_of_mem h1
  | cons x xs => exact mulFrom S x xs

theorem addL_cons (S : List ℤ) (x : Ex) (xs : List Ex) : CTo S (Natural.addL (x :: xs)) S :=
  addFrom S x xs

theorem mulL_cons (S : List ℤ) (x : Ex) (xs : List Ex) : CTo S (Natural.mulL (x :: xs)) S :=
  mulFrom S x xs

theorem square (S : List ℤ) (x : Ex) : CTo S (Natural.square x) S := mulL_cons S x [x]

theorem scale {S : List ℤ} {n : ℤ} (hn : n ∈ S) (x : Ex) : CTo S (Natural.scale n x) S :=
  bind (constant_of_mem hn) fun c => mulL_cons S c [x]

theorem seqM_nil (S : List ℤ) : CTo S (Natural.seqM ([] : List (NM α))) S := pure S _

theorem seqM_cons {S : List ℤ} {m : NM α} {ms : List (NM α)} (hm : CTo S m S)
    (hms : CTo S (Natural.seqM ms) S) : CTo S (Natural.seqM (m :: ms)) S :=
  bind hm fun _ => bind hms fun _ => pure S _

theorem seqM_map {γ : Type} {S : List ℤ} (l : List γ) (g : γ → NM α) (h : ∀ x, CTo S (g x) S) :
    CTo S (Natural.seqM (l.map g)) S := by
  induction l with
  | nil => exact seqM_nil S
  | cons x l ih => exact seqM_cons (h x) ih

theorem andM {S : List ℤ} {ms : List (NM NForm)} (h : CTo S (Natural.seqM ms) S) :
    CTo S (Natural.andM ms) S := bind h fun _ => pure S _

end CTo

/-- The constants `0, 1, 2` are present. -/
abbrev Has012 (S : List ℤ) : Prop := (0 : ℤ) ∈ S ∧ (1 : ℤ) ∈ S ∧ (2 : ℤ) ∈ S

set_option hygiene false in
/-- Proves `CTo S m S` for a construction requesting only `0, 1, 2`, given `hS : Has012 S`. -/
macro "cto_tac" : tactic => `(tactic| repeat' (first
  | (intro _)
  | (with_reducible apply CTo.pure _ _)
  | (with_reducible apply CTo.fresh _)
  | (with_reducible apply CTo.note _ _)
  | (with_reducible apply CTo.constant_of_mem hS.2.1)
  | (with_reducible apply CTo.constant_of_mem hS.2.2)
  | (with_reducible apply CTo.constant_of_mem hS.1)
  | (with_reducible apply CTo.addL hS.1 _)
  | (with_reducible apply CTo.mulL hS.2.1 _)
  | (with_reducible apply CTo.square _ _)
  | (with_reducible apply CTo.scale hS.2.2 _)
  | (with_reducible apply CTo.callPower _ _ _ _)
  | (with_reducible apply CTo.seqM_nil _)
  | (with_reducible apply cto_lt hS _ _)
  | (with_reducible apply cto_odd hS _)
  | (with_reducible apply cto_power hS _ _ _)
  | (with_reducible apply cto_binomial hS _ _ _)
  | (with_reducible apply cto_orthogonal hS _ _)
  | (with_reducible apply cto_mask hS _ _)
  | (with_reducible apply cto_bitAnd hS _ _ _)
  | (with_reducible apply CTo.andM)
  | (with_reducible apply CTo.seqM_cons)
  | (with_reducible apply CTo.bind)))

section Macros

variable {S : List ℤ}

theorem cto_lt (hS : Has012 S) (a b : Ex) : CTo S (Natural.lt a b) S := by
  unfold Natural.lt; cto_tac

theorem cto_odd (hS : Has012 S) (x : Ex) : CTo S (Natural.odd x) S := by
  unfold Natural.odd; cto_tac

theorem cto_power (_ : Has012 S) (P Q R : Ex) : CTo S (Natural.power .hierarchical P Q R) S :=
  CTo.bind (CTo.note S _) fun _ => CTo.callPower S P Q R

theorem cto_binomial (hS : Has012 S) (C N K : Ex) :
    CTo S (Natural.binomial .hierarchical C N K) S := by
  unfold Natural.binomial; cto_tac

theorem cto_orthogonal (hS : Has012 S) (a b : Ex) :
    CTo S (Natural.orthogonal .hierarchical a b) S := by
  unfold Natural.orthogonal; cto_tac

theorem cto_mask (hS : Has012 S) (a b : Ex) : CTo S (Natural.mask .hierarchical a b) S := by
  unfold Natural.mask; cto_tac

theorem cto_bitAnd (hS : Has012 S) (z x y : Ex) :
    CTo S (Natural.bitAnd .hierarchical z x y) S := by
  unfold Natural.bitAnd; cto_tac

end Macros

/-! ### The packed construction -/

section PackedItems

variable {S : List ℤ}

theorem CTo.seqM_cons' {α : Type} {S T U : List ℤ} {m : NM α} {ms : List (NM α)}
    (hm : CTo S m T) (hms : CTo T (Natural.seqM ms) U) : CTo S (Natural.seqM (m :: ms)) U :=
  CTo.bind hm fun _ => CTo.bind hms fun _ => CTo.pure U _

theorem cto_freshN (S : List ℤ) (n : ℕ) : CTo S (Packed.freshN n) S := by
  induction n with
  | zero => exact CTo.pure S _
  | succ n ih => exact CTo.bind (CTo.fresh S) fun _ => CTo.bind ih fun _ => CTo.pure S _

theorem cto_seqConcat_map {γ : Type} (l : List γ) (g : γ → NM (List NForm))
    (h : ∀ x, CTo S (g x) S) : CTo S (Packed.seqConcat (l.map g)) S := by
  induction l with
  | nil => exact CTo.pure S _
  | cons x l ih => exact CTo.bind (h x) fun _ => CTo.bind ih fun _ => CTo.pure S _

theorem cto_appendM {m₁ m₂ : NM (List NForm)} {S T U : List ℤ} (h₁ : CTo S m₁ T)
    (h₂ : CTo T m₂ U) : CTo S (Packed.appendM m₁ m₂) U :=
  CTo.bind h₁ fun _ => CTo.bind h₂ fun _ => CTo.pure U _

theorem cto_registerMasks (hS : Has012 S) (K D T F Rj Nj : Ex) :
    CTo S (Packed.registerMasks K D T F Rj Nj) S := by
  unfold Packed.registerMasks; cto_tac

theorem cto_registerEq (hS : Has012 S) (B Rj ιj : Ex) (decs incs : List Ex) :
    CTo S (Packed.registerEq B Rj ιj decs incs) S := by
  unfold Packed.registerEq; cto_tac

theorem cto_stateEq (hS : Has012 S) (B Si e : Ex) (ins : List Ex) :
    CTo S (Packed.stateEq B Si e ins) S := by
  unfold Packed.stateEq; cto_tac

theorem cto_subBranches (hS : Has012 S) (zero : Ex) (S' N : List Ex) (i : ℕ) (p : Program) :
    CTo S (Packed.subBranches zero S' N i p) S := by
  induction p generalizing i with
  | nil => exact CTo.pure S _
  | cons ins rest ih =>
    cases ins with
    | inc j x => simpa [Packed.subBranches] using ih (i + 1)
    | halt => simpa [Packed.subBranches] using ih (i + 1)
    | dec j x y =>
      unfold Packed.subBranches
      refine CTo.bind (CTo.fresh S) fun V => CTo.bind (CTo.fresh S) fun W =>
        CTo.bind ?_ fun fs => CTo.bind (ih (i + 1)) fun _ => CTo.pure S _
      cto_tac

theorem cto_items2 (hS : Has012 S) (zero one K B T F D : Ex) (S' : List Ex) :
    CTo S (Packed.items2 zero one K B T F D S') S := by
  unfold Packed.items2; cto_tac

theorem cto_items3 (hS : Has012 S) (F : Ex) (S' : List Ex) : CTo S (Packed.items3 F S') S :=
  CTo.seqM_map _ _ fun x => cto_mask hS x F

theorem cto_items4 (hS : Has012 S) (r : ℕ) (zero K D T F : Ex) (R N : List Ex) :
    CTo S (Packed.items4 r zero K D T F R N) S :=
  cto_seqConcat_map _ _ fun _ => cto_registerMasks hS ..

theorem cto_items6 (hS : Has012 S) (p : Program) (r : ℕ) (a : List Ex) (zero B : Ex)
    (R S' : List Ex) (vw : List (ℕ × Ex × Ex)) : CTo S (Packed.items6 p r a zero B R S' vw) S :=
  CTo.seqM_map _ _ fun _ => cto_registerEq hS ..

theorem cto_items7 (hS : Has012 S) (p : Program) (zero one B : Ex) (S' : List Ex)
    (vw : List (ℕ × Ex × Ex)) : CTo S (Packed.items7 p zero one B S' vw) S :=
  CTo.seqM_map _ _ fun _ => cto_stateEq hS ..

theorem cto_lt_of_one {a b : Ex} (h1 : (1 : ℤ) ∈ S) : CTo S (Natural.lt a b) S := by
  unfold Natural.lt
  exact CTo.bind (CTo.note S _) fun _ => CTo.bind (CTo.fresh S) fun _ =>
    CTo.bind (CTo.constant_of_mem h1) fun _ => CTo.bind (CTo.addL_cons S _ _) fun _ =>
      CTo.pure S _

/-- Item 1 requests `2`, `4` and the program length, in this order. -/
theorem cto_items1 (p : Program) (hp : 4 < p.length) (a : List Ex) (zero q c K B T : Ex) :
    CTo [0, 1] (Packed.items1 p a zero q c K B T) [0, 1, 2, 4, (p.length : ℤ)] := by
  have hL : addC (p.length : ℤ) [0, 1, 2, 4] = [0, 1, 2, 4, (p.length : ℤ)] := by
    unfold addC
    rw [if_neg]
    · rfl
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      omega
  have hS5 : Has012 [0, 1, 2, 4, (p.length : ℤ)] := ⟨by simp, by simp, by simp⟩
  unfold Packed.items1
  rw [Packed.seqM_append]
  refine CTo.bind ?_ fun _ => CTo.bind (CTo.seqM_map _ _ fun ai => cto_lt hS5 ai K) fun _ =>
    CTo.pure _ _
  refine CTo.seqM_cons' (cto_lt_of_one (by simp)) ?_
  refine CTo.seqM_cons' ((CTo.bind (CTo.constant _ 2) fun _ =>
    CTo.bind (CTo.note _ _) fun _ => CTo.callPower _ _ _ _).congr (T' := [0, 1, 2]) (by decide)) ?_
  refine CTo.seqM_cons' ((CTo.bind (CTo.bind (CTo.constant _ 4) fun _ => CTo.mulL_cons _ _ _)
    fun _ => CTo.pure _ _).congr (T' := [0, 1, 2, 4]) (by decide)) ?_
  refine CTo.seqM_cons' (CTo.bind ((CTo.constant _ _).congr hL) fun _ =>
    cto_lt_of_one (by simp)) ?_
  refine CTo.seqM_cons' (CTo.bind (CTo.note _ _) fun _ => CTo.callPower _ _ _ _) ?_
  exact CTo.seqM_nil _

end PackedItems

theorem cto_packedFormulas (p : Program) (hp : 4 < p.length) (r : ℕ) (a : List Ex)
    (zero one q c K B T F D : Ex) (R N S' : List Ex) :
    CTo [0, 1] (Packed.packedFormulas p r a zero one q c K B T F D R N S')
      [0, 1, 2, 4, (p.length : ℤ)] := by
  have hS5 : Has012 [0, 1, 2, 4, (p.length : ℤ)] := ⟨by simp, by simp, by simp⟩
  unfold Packed.packedFormulas
  exact cto_appendM (cto_items1 p hp a zero q c K B T) (cto_appendM (cto_items2 hS5 ..)
    (cto_appendM (cto_items3 hS5 ..) (cto_appendM (cto_items4 hS5 ..)
      (CTo.bind (cto_subBranches hS5 ..) fun _ => cto_appendM (CTo.pure _ _)
        (cto_appendM (cto_items6 hS5 ..) (cto_items7 hS5 ..))))))

theorem cto_construction (p : Program) (hp : 4 < p.length) (r k : ℕ) :
    CTo [] (Packed.construction p r k) [0, 1, 2, 4, (p.length : ℤ)] := by
  unfold Packed.construction
  refine CTo.bind ((CTo.constant [] 0).congr (T' := [0]) (by decide)) fun _ =>
    CTo.bind ((CTo.constant [0] 1).congr (T' := [0, 1]) (by decide)) fun _ =>
    CTo.bind (CTo.fresh _) fun _ => CTo.bind (CTo.fresh _) fun _ => CTo.bind (CTo.fresh _) fun _ =>
    CTo.bind (CTo.fresh _) fun _ => CTo.bind (CTo.fresh _) fun _ => CTo.bind (CTo.fresh _) fun _ =>
    CTo.bind (CTo.fresh _) fun _ => CTo.bind (cto_freshN _ r) fun _ =>
    CTo.bind (cto_freshN _ r) fun _ => CTo.bind (cto_freshN _ p.length) fun _ =>
    CTo.bind (cto_packedFormulas p hp ..) fun _ => CTo.pure _ _

/-! ### The node encoding -/

mutual

/-- The formula has an equation atom. -/
def hasEq : NForm → Bool
  | .eq _ _ => true
  | .atom _ => false
  | .call _ _ _ _ _ => false
  | .and fs => hasEqs fs
  | .or fs => hasEqs fs

/-- Some formula of the list has an equation atom. -/
def hasEqs : List NForm → Bool
  | [] => false
  | f :: fs => hasEq f || hasEqs fs

end

/-- The constant list after encoding a formula (with an equation atom iff `b`). -/
def encC (b : Bool) (S : List ℤ) : List ℤ := if b then addC (-1) S else S

theorem mem_encC {b : Bool} {S : List ℤ} {d : ℤ} (h : d ∈ S) : d ∈ encC b S := by
  unfold encC; split_ifs
  · exact mem_addC_of_mem h
  · exact h

theorem encC_encC (b₁ b₂ : Bool) (S : List ℤ) : encC b₂ (encC b₁ S) = encC (b₁ || b₂) S := by
  cases b₁ <;> cases b₂ <;> simp [encC, addC_idem]

mutual

theorem cto_encode (τ : Syntax.ExPoly) : ∀ (φ : NForm) (S : List ℤ), (0 : ℤ) ∈ S → (1 : ℤ) ∈ S →
    CTo S (φ.encode τ) (encC (hasEq φ) S)
  | .eq _ _, S, _, _ =>
    CTo.bind (CTo.bind (CTo.constant S (-1)) fun _ => CTo.mulL_cons _ _ _) fun _ =>
      CTo.addL_cons _ _ _
  | .atom _, S, _, _ => CTo.pure S _
  | .call _ _ _ _ _, S, _, _ => CTo.pure S _
  | .and fs, S, h0, h1 =>
    CTo.bind (cto_encodeList τ fs S h0 h1) fun es =>
      CTo.bind (CTo.seqM_map es _ fun x => CTo.square _ x) fun sq => CTo.addL (mem_encC h0) sq
  | .or fs, S, h0, h1 =>
    CTo.bind (cto_encodeList τ fs S h0 h1) fun es => CTo.mulL (mem_encC h1) es

theorem cto_encodeList (τ : Syntax.ExPoly) : ∀ (fs : List NForm) (S : List ℤ), (0 : ℤ) ∈ S →
    (1 : ℤ) ∈ S → CTo S (NForm.encodeList τ fs) (encC (hasEqs fs) S)
  | [], S, _, _ => CTo.pure S _
  | f :: fs, S, h0, h1 =>
    (CTo.bind (cto_encode τ f S h0 h1) fun _ =>
      CTo.bind (cto_encodeList τ fs _ (mem_encC h0) (mem_encC h1)) fun _ =>
        CTo.pure _ _).congr (encC_encC ..)

end

theorem hasEq_construction (p : Program) (r k : ℕ) (s : State) :
    hasEq (Packed.construction p r k s).1 = true := rfl

/-! ### The compiled circuit -/

theorem constList_init (k : ℕ) : constList (State.init k).nodes = [] := by
  simp [State.init, constList, List.filterMap_map, Function.comp_def, constOf]

/-- The constant list of the compiled circuit: `0, 1, 2, 4, m, -1`. -/
theorem compiled_constList (p : Program) (hp : 4 < p.length) (r k : ℕ) :
    constList (Packed.compiled p r k).nodes = [0, 1, 2, 4, (p.length : ℤ), -1] := by
  rw [Packed.compiled, NM.toCircuit_nodes]
  have h1 := (cto_construction p hp r k).run _ (constList_init k)
  have h2 := (cto_encode Syntax.ExPoly.empty (Packed.construction p r k (State.init k)).1 _
    (by simp) (by simp)).run _ h1
  rw [h2, hasEq_construction]
  unfold encC addC
  rw [if_pos rfl, if_neg]
  · rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    omega

theorem countKind_const_eq (l : List NatNode) : countKind .const l = (constList l).length := by
  induction l with
  | nil => rfl
  | cons n l ih =>
    unfold countKind constList at *
    rw [List.countP_cons, List.filterMap_cons, ih]
    cases n <;> simp [nodeKind, constOf]

/-- **The constants of the halting circuit**: `0, 1, 2, 4, 1399, -1` in node order (the last
item of `HaltingNodeCheck`). -/
theorem haltingCircuit_constList : constList haltingCircuit.nodes = [0, 1, 2, 4, 1399, -1] := by
  have h := compiled_constList interpreter (by rw [interpreter_length]; norm_num) 204 2
  rw [interpreter_length] at h
  exact h

/-- **The constant-node count of the halting circuit**, `6`. -/
theorem haltingCircuit_constNodes : countKind .const haltingCircuit.nodes = 6 := by
  rw [countKind_const_eq, haltingCircuit_constList]
  rfl

end ZInQ.Compiler.NodeCheck
