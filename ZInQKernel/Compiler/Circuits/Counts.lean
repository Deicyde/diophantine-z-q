import ZInQKernel.Compiler.Circuits.Construction

/-!
# Allocation counts of natural constructions

`Counts m v b L` says that, from every state, the construction `m` takes `v` fresh explicit
variables and `b` power blocks (so the counter grows by `v + 79 b`), creates `b` call nodes, and
appends `L` to the macro log. Expression constructions count nothing, and counts add up along
`>>=`. We record the counts of every gadget and macro: `lt`, `divides`, `odd` one variable,
`congruent` two, `alpha` `23`, the flat power macro `79`, the hierarchical one one block, and
in hierarchical mode `binomial` `7` variables and `3` blocks, `orthogonal` and `mask` `9` and
`3`, `bitAnd` `29` and `9`.

(Helper lemmas for `compiler/natural/packed/packed-counts.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Natural

/-- Call nodes. -/
def NatNode.isCall : NatNode → Bool
  | .call _ _ _ _ => true
  | _ => false

/-- The number of call nodes of a state. -/
def callCount (s : State) : ℕ := s.nodes.countP NatNode.isCall

/-- Allocation counts of a construction. -/
def Counts {α : Type} (m : NM α) (v b : ℕ) (L : List MacroKind) : Prop :=
  ∀ s, (m s).2.next = s.next + v + powerWitnesses * b ∧ (m s).2.vars.length = s.vars.length + v ∧
    (m s).2.blocks.length = s.blocks.length + b ∧ callCount (m s).2 = callCount s + b ∧
    (m s).2.log = s.log ++ L

namespace Counts

variable {α β : Type}

theorem pure (a : α) : Counts (Pure.pure a : NM α) 0 0 [] := fun s => by simp

theorem bind {m : NM α} {f : α → NM β} {v₁ b₁ v₂ b₂ : ℕ} {L₁ L₂ : List MacroKind}
    (hm : Counts m v₁ b₁ L₁) (hf : ∀ a, Counts (f a) v₂ b₂ L₂) :
    Counts (m >>= f) (v₁ + v₂) (b₁ + b₂) (L₁ ++ L₂) := fun s => by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hm s
  obtain ⟨k1, k2, k3, k4, k5⟩ := hf (m s).1 (m s).2
  simp only [NM.bind_apply]
  refine ⟨by rw [k1, h1]; ring, by rw [k2, h2]; ring, by rw [k3, h3]; ring, by rw [k4, h4]; ring,
    by rw [k5, h5, List.append_assoc]⟩

/-- A bind whose continuation is counted only on the values the first construction can
return. -/
theorem bind' {m : NM α} {f : α → NM β} {v₁ b₁ v₂ b₂ : ℕ} {L₁ L₂ : List MacroKind}
    {P : α → Prop} (hm : Counts m v₁ b₁ L₁) (hP : ∀ s, P (m s).1)
    (hf : ∀ a, P a → Counts (f a) v₂ b₂ L₂) :
    Counts (m >>= f) (v₁ + v₂) (b₁ + b₂) (L₁ ++ L₂) := fun s => by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hm s
  obtain ⟨k1, k2, k3, k4, k5⟩ := hf (m s).1 (hP s) (m s).2
  simp only [NM.bind_apply]
  refine ⟨by rw [k1, h1]; ring, by rw [k2, h2]; ring, by rw [k3, h3]; ring, by rw [k4, h4]; ring,
    by rw [k5, h5, List.append_assoc]⟩

theorem bind_eq {m : NM α} {f : α → NM β} {v₁ b₁ v₂ b₂ v b : ℕ} {L₁ L₂ L : List MacroKind}
    (hf : ∀ a, Counts (f a) v₂ b₂ L₂) (hm : Counts m v₁ b₁ L₁) (hv : v₁ + v₂ = v)
    (hb : b₁ + b₂ = b) (hL : L₁ ++ L₂ = L) : Counts (m >>= f) v b L := by
  subst hv hb hL; exact bind hm hf

theorem congr {m : NM α} {v b v' b' : ℕ} {L L' : List MacroKind} (h : Counts m v b L)
    (hv : v = v') (hb : b = b') (hL : L = L') : Counts m v' b' L' := by
  subst hv hb hL; exact h

theorem node {n : NatNode} (hn : n.isCall = false) : Counts (Natural.node n) 0 0 [] := fun s => by
  unfold Natural.node callCount
  split
  · simp
  · simp [List.countP_append, hn]

theorem constant (c : ℤ) : Counts (Natural.constant c) 0 0 [] := by
  exact (node (n := .const c) rfl).bind fun i => pure (⟨i, MvPolynomial.C c⟩ : Ex)

theorem addFrom (acc : Ex) (l : List Ex) : Counts (Natural.addFrom acc l) 0 0 [] := by
  induction l generalizing acc with
  | nil => exact pure acc
  | cons y ys ih =>
    have := (node (n := .add acc.node y.node) rfl).bind fun i => ih ⟨i, acc.poly + y.poly⟩
    simpa [Natural.addFrom] using this

theorem mulFrom (acc : Ex) (l : List Ex) : Counts (Natural.mulFrom acc l) 0 0 [] := by
  induction l generalizing acc with
  | nil => exact pure acc
  | cons y ys ih =>
    have := (node (n := .mul acc.node y.node) rfl).bind fun i => ih ⟨i, acc.poly * y.poly⟩
    simpa [Natural.mulFrom] using this

theorem addL (l : List Ex) : Counts (Natural.addL l) 0 0 [] := by
  cases l with
  | nil => exact constant 0
  | cons x xs => exact addFrom x xs

theorem mulL (l : List Ex) : Counts (Natural.mulL l) 0 0 [] := by
  cases l with
  | nil => exact constant 1
  | cons x xs => exact mulFrom x xs

theorem square (x : Ex) : Counts (Natural.square x) 0 0 [] := mulL _

theorem scale (n : ℤ) (x : Ex) : Counts (Natural.scale n x) 0 0 [] := by
  exact (constant n).bind fun c => mulL [c, x]

theorem fresh : Counts Natural.fresh 1 0 [] := fun s => by
  have h := (node (n := .var s.next) rfl)
    { s with next := s.next + 1, vars := s.vars ++ [(s.next, .witness)] }
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  simp only [Natural.fresh]
  exact ⟨by simp [h1], by simp [h2], by simp [h3], by simpa [callCount] using h4, by simp [h5]⟩

theorem callPower (P Q R : Ex) : Counts (Natural.callPower P Q R) 0 1 [] := fun s => by
  simp [Natural.callPower, callCount, List.countP_append, NatNode.isCall]

theorem note (k : MacroKind) : Counts (Natural.note k) 0 0 [k] := fun s => by
  simp [Natural.note, callCount]

theorem seqM_cons {m : NM α} {ms : List (NM α)} {v₁ b₁ v₂ b₂ : ℕ} {L₁ L₂ : List MacroKind}
    (hm : Counts m v₁ b₁ L₁) (hms : Counts (seqM ms) v₂ b₂ L₂) :
    Counts (seqM (m :: ms)) (v₁ + v₂) (b₁ + b₂) (L₁ ++ L₂) := by
  have := hm.bind fun a => hms.bind fun as => pure (a :: as)
  simpa [seqM] using this

theorem seqM_cons_eq {m : NM α} {ms : List (NM α)} {v₁ b₁ v₂ b₂ v b : ℕ}
    {L₁ L₂ L : List MacroKind} (hm : Counts m v₁ b₁ L₁) (hms : Counts (seqM ms) v₂ b₂ L₂)
    (hv : v₁ + v₂ = v) (hb : b₁ + b₂ = b) (hL : L₁ ++ L₂ = L) : Counts (seqM (m :: ms)) v b L := by
  subst hv hb hL; exact seqM_cons hm hms

theorem seqM_nil : Counts (seqM ([] : List (NM α))) 0 0 [] := pure _

/-- A list of constructions with the same counts. -/
theorem seqM_map {γ : Type} (l : List γ) (g : γ → NM α) {v b : ℕ} {L : List MacroKind}
    (h : ∀ x, Counts (g x) v b L) :
    Counts (seqM (l.map g)) (l.length * v) (l.length * b) (List.replicate l.length L).flatten := by
  induction l with
  | nil => simpa using seqM_nil
  | cons x xs ih =>
    refine (seqM_cons (h x) ih).congr ?_ ?_ ?_
    · simp [Nat.succ_mul, add_comm]
    · simp [Nat.succ_mul, add_comm]
    · simp [List.replicate_succ]

theorem andM {ms : List (NM NForm)} {v b : ℕ} {L : List MacroKind} (h : Counts (seqM ms) v b L) :
    Counts (Natural.andM ms) v b L := by
  exact (h.bind fun fs => pure (NForm.and fs)).congr rfl rfl (List.append_nil L)

theorem orM {ms : List (NM NForm)} {v b : ℕ} {L : List MacroKind} (h : Counts (seqM ms) v b L) :
    Counts (Natural.orM ms) v b L := by
  exact (h.bind fun fs => pure (NForm.or fs)).congr rfl rfl (List.append_nil L)

end Counts

set_option hygiene false in
/-- Counts a construction built from the builder operations and counted macros. -/
macro "counts_tac" : tactic => `(tactic| repeat' (first
  | with_reducible exact Counts.pure _
  | with_reducible exact Counts.fresh
  | with_reducible exact Counts.note _
  | with_reducible exact Counts.constant _
  | with_reducible exact Counts.addL _
  | with_reducible exact Counts.mulL _
  | with_reducible exact Counts.square _
  | with_reducible exact Counts.scale _ _
  | with_reducible exact Counts.callPower _ _ _
  | with_reducible exact Counts.seqM_nil
  | with_reducible exact Counts.lt _ _
  | with_reducible exact Counts.divides _ _
  | with_reducible exact Counts.congruent _ _ _
  | with_reducible exact Counts.odd _
  | with_reducible exact Counts.alpha _ _ _
  | with_reducible exact Counts.powerFlat _ _ _
  | with_reducible exact Counts.power_hierarchical _ _ _
  | with_reducible exact Counts.binomial _ _ _
  | with_reducible exact Counts.orthogonal _ _
  | with_reducible exact Counts.mask _ _
  | with_reducible exact Counts.bitAnd _ _ _
  | (with_reducible apply Counts.andM)
  | (with_reducible apply Counts.orM)
  | (with_reducible apply Counts.seqM_cons_eq)
  | (with_reducible apply Counts.bind_eq; intro _)))

set_option hygiene false in
/-- Proves `Counts m v b L` for the construction `m` unfolded by `u`. -/
macro "counts_of " u:ident : tactic => `(tactic| (
  unfold $u:ident
  counts_tac
  all_goals first | rfl | simp))

/-! ### Counts of the gadgets and macros -/

theorem Counts.lt (a b : Ex) : Counts (Natural.lt a b) 1 0 [.lt] := by
  counts_of Natural.lt

theorem Counts.divides (a b : Ex) : Counts (Natural.divides a b) 1 0 [.divides] := by
  counts_of Natural.divides

theorem Counts.congruent (a M b : Ex) : Counts (Natural.congruent a M b) 2 0 [.congruent] := by
  counts_of Natural.congruent

theorem Counts.odd (x : Ex) : Counts (Natural.odd x) 1 0 [.odd] := by
  counts_of Natural.odd

/-- The log of `alpha`. -/
def alphaLog : List MacroKind :=
  [.alpha, .lt, .lt, .divides, .congruent, .congruent, .lt, .lt, .lt, .congruent, .lt, .congruent]

/-- The log of the flat power macro body. -/
def powerFlatLog : List MacroKind :=
  [.lt, .lt] ++ alphaLog ++ [.lt] ++ alphaLog ++ alphaLog ++ [.congruent]

/-- The log of `binomial` in hierarchical mode. -/
def binomialLog : List MacroKind := [.binomial, .power, .power, .power, .lt, .lt]

/-- The log of `orthogonal` in hierarchical mode. -/
def orthogonalLog : List MacroKind := .orthogonal :: binomialLog ++ [.odd]

/-- The log of `mask` in hierarchical mode. -/
def maskLog : List MacroKind := .mask :: binomialLog ++ [.odd]

/-- The log of `bitAnd` in hierarchical mode. -/
def bitAndLog : List MacroKind := .bitAnd :: orthogonalLog ++ orthogonalLog ++ orthogonalLog

theorem Counts.alpha (X b N : Ex) : Counts (Natural.alpha X b N) 23 0 alphaLog := by
  counts_of Natural.alpha

theorem Counts.powerFlat (P Q R : Ex) : Counts (Natural.powerFlat P Q R) 79 0 powerFlatLog := by
  counts_of Natural.powerFlat

theorem Counts.power_flat (P Q R : Ex) :
    Counts (Natural.power .flat P Q R) 79 0 (.power :: powerFlatLog) :=
  (Counts.note _).bind (fun _ => Counts.powerFlat P Q R)

theorem Counts.power_hierarchical (P Q R : Ex) :
    Counts (Natural.power .hierarchical P Q R) 0 1 [.power] :=
  (Counts.note _).bind (fun _ => Counts.callPower P Q R)

theorem Counts.binomial (C N K : Ex) :
    Counts (Natural.binomial .hierarchical C N K) 7 3 binomialLog := by
  counts_of Natural.binomial

theorem Counts.orthogonal (a b : Ex) :
    Counts (Natural.orthogonal .hierarchical a b) 9 3 orthogonalLog := by
  counts_of Natural.orthogonal

theorem Counts.mask (a b : Ex) : Counts (Natural.mask .hierarchical a b) 9 3 maskLog := by
  counts_of Natural.mask

theorem Counts.bitAnd (z x y : Ex) :
    Counts (Natural.bitAnd .hierarchical z x y) 29 9 bitAndLog := by
  counts_of Natural.bitAnd

mutual

theorem counts_encode (τ : Syntax.ExPoly) : ∀ φ : NForm, Counts (φ.encode τ) 0 0 []
  | .eq a b => (Counts.scale (-1) b).bind fun c => Counts.addL [a, c]
  | .atom f => Counts.pure f
  | .call P Q R w j => Counts.pure _
  | .and fs => by
    have hsq : ∀ es : List Ex, Counts (seqM (es.map Natural.square) >>= Natural.addL) 0 0 [] :=
      fun es => ((Counts.seqM_map es Natural.square fun x => Counts.square x).bind fun sq =>
        Counts.addL sq).congr (by simp) (by simp) (by simp)
    exact (counts_encodeList τ fs).bind hsq
  | .or fs => (counts_encodeList τ fs).bind fun es => Counts.mulL es

theorem counts_encodeList (τ : Syntax.ExPoly) : ∀ fs : List NForm,
    Counts (NForm.encodeList τ fs) 0 0 []
  | [] => Counts.pure _
  | f :: fs => (counts_encode τ f).bind fun e =>
      (counts_encodeList τ fs).bind fun es => Counts.pure (e :: es)

end

end ZInQ.Compiler.Natural
