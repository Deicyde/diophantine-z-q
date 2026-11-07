import ZInQKernel.Compiler.NodeBound.Defs

/-!
# Upper bounds on the nodes created by a natural construction

`Up P m a b Q`: run from a state whose node list satisfies `P`, the construction `m` only extends
the node list, creates at most `a` addition and `b` multiplication nodes, and ends with a result
and a node list satisfying `Q`. Upper bounds need no absence argument: a node call creates at
most one node of its kind, and none if the node is already present (a *hit*). Presence is
monotone (the node list only grows), so the facts carried by the pre- and postconditions are
presence facts: `n ∈ l` and `l.idxOf? n = some i`.
-/

namespace ZInQ.Compiler.NodeBound

open Natural Universal

/-- A property of node lists that survives extensions. -/
structure Mono (P : List NatNode → Prop) : Prop where
  mono : ∀ l l', l <+: l' → P l → P l'

namespace Mono

theorem and {P Q : List NatNode → Prop} (hP : Mono P) (hQ : Mono Q) : Mono fun l => P l ∧ Q l :=
  ⟨fun l l' h hl => ⟨hP.mono l l' h hl.1, hQ.mono l l' h hl.2⟩⟩

theorem const (p : Prop) : Mono fun _ => p := ⟨fun _ _ _ h => h⟩

theorem mem (n : NatNode) : Mono fun l => n ∈ l := ⟨fun _ _ h hl => h.subset hl⟩

theorem idxOf? (n : NatNode) (i : ℕ) : Mono fun l => l.idxOf? n = some i := by
  refine ⟨fun l l' ⟨t, ht⟩ hl => ?_⟩
  subst ht
  rw [List.idxOf?_eq_some_iff] at hl ⊢
  obtain ⟨hi, hn, hj⟩ := hl
  refine ⟨by simp; omega, by rw [List.getElem_append_left hi]; exact hn, fun j hji => ?_⟩
  rw [List.getElem_append_left (by omega)]
  exact hj j hji

theorem forall_mem {β : Type} (L : List β) {V : β → List NatNode → Prop} (hV : ∀ x, Mono (V x)) :
    Mono fun l => ∀ x ∈ L, V x l := ⟨fun l l' h hl x hx => (hV x).mono l l' h (hl x hx)⟩

theorem forall' {β : Type} {V : β → List NatNode → Prop} (hV : ∀ x, Mono (V x)) :
    Mono fun l => ∀ x, V x l := ⟨fun l l' h hl x => (hV x).mono l l' h (hl x)⟩

theorem imp (p : Prop) {V : List NatNode → Prop} (hV : Mono V) : Mono fun l => p → V l :=
  ⟨fun l l' h hl hp => hV.mono l l' h (hl hp)⟩

end Mono

theorem mem_of_idxOf? {l : List NatNode} {n : NatNode} {i : ℕ} (h : l.idxOf? n = some i) :
    n ∈ l := by
  rw [← List.isSome_idxOf?, h]; rfl

/-- The number of addition nodes. -/
abbrev cA (l : List NatNode) : ℕ := countKind .add l

/-- The number of multiplication nodes. -/
abbrev cM (l : List NatNode) : ℕ := countKind .mul l

/-- From a node list satisfying `P`, `m` only extends the node list, creates at most `a`
addition and `b` multiplication nodes, and ends in `Q`. -/
structure Up {α : Type} (P : List NatNode → Prop) (m : NM α) (a b : ℕ)
    (Q : α → List NatNode → Prop) : Prop where
  run : ∀ s : State, P s.nodes → s.nodes <+: (m s).2.nodes ∧
    cA (m s).2.nodes ≤ cA s.nodes + a ∧ cM (m s).2.nodes ≤ cM s.nodes + b ∧
    Q (m s).1 (m s).2.nodes

namespace Up

variable {α β : Type} {P P' : List NatNode → Prop} {Q Q' : α → List NatNode → Prop}
  {R : β → List NatNode → Prop} {m : NM α} {f : α → NM β} {a b a' b' : ℕ}

theorem bind (hP : Mono P) (hm : Up P m a b Q) (hf : ∀ x, Up (fun l => P l ∧ Q x l) (f x) a' b' R) :
    Up P (m >>= f) (a + a') (b + b') R := ⟨fun s hs => by
  obtain ⟨h1, h2, h3, h4⟩ := hm.run s hs
  obtain ⟨k1, k2, k3, k4⟩ := (hf (m s).1).run (m s).2 ⟨hP.mono _ _ h1 hs, h4⟩
  rw [NM.bind_apply]
  exact ⟨h1.trans k1, by omega, by omega, k4⟩⟩

theorem pure {x : α} (h : ∀ l, P l → Q x l) : Up P (Pure.pure x : NM α) 0 0 Q :=
  ⟨fun s hs => ⟨List.prefix_refl _, by simp, by simp, h _ hs⟩⟩

theorem weaken (h : Up P m a b Q) (ha : a ≤ a') (hb : b ≤ b') : Up P m a' b' Q :=
  ⟨fun s hs => by
    obtain ⟨h1, h2, h3, h4⟩ := h.run s hs
    exact ⟨h1, by omega, by omega, h4⟩⟩

theorem post (h : Up P m a b Q) (hQ : ∀ x l, Q x l → Q' x l) : Up P m a b Q' :=
  ⟨fun s hs => by
    obtain ⟨h1, h2, h3, h4⟩ := h.run s hs
    exact ⟨h1, h2, h3, hQ _ _ h4⟩⟩

theorem pre (h : Up P m a b Q) (hP : ∀ l, P' l → P l) : Up P' m a b Q :=
  ⟨fun s hs => h.run s (hP _ hs)⟩

/-- Adding a monotone frame to the pre- and postcondition. -/
theorem frame {F : List NatNode → Prop} (hF : Mono F) (h : Up P m a b Q) :
    Up (fun l => P l ∧ F l) m a b (fun x l => Q x l ∧ F l) :=
  ⟨fun s hs => by
    obtain ⟨h1, h2, h3, h4⟩ := h.run s hs.1
    exact ⟨h1, h2, h3, h4, hF.mono _ _ h1 hs.2⟩⟩

theorem congr_m {m' : NM α} (h : Up P m a b Q) (he : m = m') : Up P m' a b Q := he ▸ h

end Up

/-! ### Primitives -/

theorem countKind_append_singleton (κ : NodeKind) (l : List NatNode) (n : NatNode) :
    countKind κ (l ++ [n]) = countKind κ l + if nodeKind n = κ then 1 else 0 := by
  rw [countKind_append]
  simp [countKind, List.countP_cons]

theorem node_run (n : NatNode) (s : State) :
    ((node n s).2.nodes = s.nodes ∨ (node n s).2.nodes = s.nodes ++ [n]) ∧
      (node n s).2.nodes.idxOf? n = some (node n s).1 := by
  unfold node
  split
  · rename_i j hj
    exact ⟨.inl rfl, hj⟩
  · rename_i hj
    refine ⟨.inr rfl, ?_⟩
    have hn : n ∉ s.nodes := List.idxOf?_eq_none_iff.1 hj
    show (s.nodes ++ [n]).idxOf? n = some s.nodes.length
    unfold List.idxOf?
    rw [List.findIdx?_append]
    have : s.nodes.findIdx? (· == n) = none := by
      rw [← List.idxOf?, List.idxOf?_eq_none_iff]; exact hn
    simp [this]

theorem node_run_hit {n : NatNode} {s : State} (h : n ∈ s.nodes) : (node n s).2.nodes = s.nodes := by
  unfold node
  split
  · rfl
  · rename_i hj
    exact absurd h (List.idxOf?_eq_none_iff.1 hj)

/-- A node call creates at most one node, of its own kind. -/
theorem Up.node (n : NatNode) :
    Up P (Natural.node n) (if nodeKind n = .add then 1 else 0) (if nodeKind n = .mul then 1 else 0)
      (fun i l => l.idxOf? n = some i) := ⟨fun s _ => by
  obtain ⟨h | h, hi⟩ := node_run n s
  · rw [h]; exact ⟨List.prefix_refl _, by omega, by omega, h ▸ hi⟩
  · rw [h]
    refine ⟨List.prefix_append _ _, ?_, ?_, h ▸ hi⟩
    · simp only [cA, countKind_append_singleton]; split_ifs <;> omega
    · simp only [cM, countKind_append_singleton]; split_ifs <;> omega⟩

theorem Up.node_add (x y : ℕ) :
    Up P (Natural.node (.add x y)) 1 0 (fun i l => l.idxOf? (.add x y) = some i) :=
  (Up.node (.add x y)).congr_m rfl |>.weaken (by simp [nodeKind]) (by simp [nodeKind])

theorem Up.node_mul (x y : ℕ) :
    Up P (Natural.node (.mul x y)) 0 1 (fun i l => l.idxOf? (.mul x y) = some i) :=
  (Up.node (.mul x y)).weaken (by simp [nodeKind]) (by simp [nodeKind])

/-- A node call on a present node creates nothing. -/
theorem Up.node_hit {n : NatNode} (h : ∀ l, P l → n ∈ l) :
    Up P (Natural.node n) 0 0 (fun i l => l.idxOf? n = some i) := ⟨fun s hs => by
  have h1 := node_run_hit (h _ hs)
  refine ⟨h1 ▸ List.prefix_refl _, by rw [h1]; omega, by rw [h1]; omega, ?_⟩
  exact (node_run n s).2⟩

theorem Up.constant (c : ℤ) :
    Up P (Natural.constant c) 0 0 (fun e l => l.idxOf? (.const c) = some e.node) := by
  have h := (Up.node (P := P) (.const c)).weaken (a' := 0) (b' := 0) (by simp [nodeKind])
    (by simp [nodeKind])
  exact ⟨fun s hs => h.run s hs⟩

theorem Up.fresh : Up P Natural.fresh 0 0 (fun _ _ => True) := ⟨fun s _ => by
  have h := (Up.node (P := fun _ => True) (.var s.next)).run
    { s with next := s.next + 1, vars := s.vars ++ [(s.next, .witness)] } trivial
  simp only [nodeKind, reduceCtorEq, ite_false, Nat.add_zero] at h
  exact ⟨h.1, h.2.1, h.2.2.1, trivial⟩⟩

theorem Up.note (k : MacroKind) : Up P (Natural.note k) 0 0 (fun _ _ => True) :=
  ⟨fun _ _ => ⟨List.prefix_refl _, le_refl _, le_refl _, trivial⟩⟩

/-! ### Encoding costs of formulas -/

mutual

/-- The number of addition nodes requested by the node encoding of a formula. -/
def encA : NForm → ℕ
  | .eq _ _ => 1
  | .atom _ => 0
  | .call _ _ _ _ _ => 0
  | .and fs => encAL fs + (fs.length - 1)
  | .or fs => encAL fs

/-- `encA` summed over a list. -/
def encAL : List NForm → ℕ
  | [] => 0
  | f :: fs => encA f + encAL fs

end

mutual

/-- The number of multiplication nodes requested by the node encoding of a formula. -/
def encM : NForm → ℕ
  | .eq _ _ => 1
  | .atom _ => 0
  | .call _ _ _ _ _ => 0
  | .and fs => encML fs + fs.length
  | .or fs => encML fs + (fs.length - 1)

/-- `encM` summed over a list. -/
def encML : List NForm → ℕ
  | [] => 0
  | f :: fs => encM f + encML fs

end

theorem encAL_append (l l' : List NForm) : encAL (l ++ l') = encAL l + encAL l' := by
  induction l with
  | nil => simp [encAL]
  | cons f l ih => simp only [List.cons_append, encAL, ih]; omega

theorem encML_append (l l' : List NForm) : encML (l ++ l') = encML l + encML l' := by
  induction l with
  | nil => simp [encML]
  | cons f l ih => simp only [List.cons_append, encML, ih]; omega

/-- A formula with encoding costs `a` and `b`. -/
structure Cost (a b : ℕ) (φ : NForm) : Prop where
  enc_a : encA φ = a
  enc_m : encM φ = b

/-- A list of `n` formulas with total encoding costs `a` and `b`. -/
structure CostL (a b n : ℕ) (φs : List NForm) : Prop where
  enc_a : encAL φs = a
  enc_m : encML φs = b
  len : φs.length = n

theorem Up.callPower (A B C : Ex) :
    Up P (Natural.callPower A B C) 0 0 (fun φ _ => Cost 0 0 φ) :=
  ⟨fun s _ => by
    refine ⟨List.prefix_append _ _, ?_, ?_, ⟨rfl, rfl⟩⟩
    · show cA (s.nodes ++ _) ≤ _
      rw [cA, countKind_append_singleton]; simp [nodeKind]
    · show cM (s.nodes ++ _) ≤ _
      rw [cM, countKind_append_singleton]; simp [nodeKind]⟩

/-! ### Monad normalization -/

theorem NM.bind_assoc' {α β γ : Type} (m : NM α) (f : α → NM β) (g : β → NM γ) :
    (m >>= f) >>= g = m >>= fun x => f x >>= g := rfl

theorem NM.pure_bind' {α β : Type} (a : α) (f : α → NM β) : (Pure.pure a : NM α) >>= f = f a :=
  rfl

end ZInQ.Compiler.NodeBound
