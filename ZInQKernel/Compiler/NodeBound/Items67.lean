import ZInQKernel.Compiler.NodeBound.Encode

/-!
# Node bounds of items 6 and 7, for one register and one state

Item 6 for a register (`registerEq`) requests `(|C| - 1) + (|A| - 1) + 3` additions and `3`
multiplications; when `A_j` is a single summand `x`, it leaves the product `B·x` behind.

Item 7 for a state (`stateEq B S_i e I`) requests `(|I| - 1) + 1` additions and one
multiplication. Three kinds of repeats are subtracted:

* `I = V, W, …` with the sum `V + W` present (built by item 5 for the same sub instruction): one
  addition fewer;
* `I = x` with the product `B·x` present (built by item 6): one multiplication fewer;
* `I` empty and the nodes `B·0` and `e + B·0` present (`ZPre`, left behind by an earlier state
  with no predecessors): nothing is created. Such a state leaves `ZPost` behind: its right side
  is the node `e + B·0`.
-/

namespace ZInQ.Compiler.NodeBound

open Natural Universal

variable {P : List NatNode → Prop}

theorem addL_up' (hP : Mono P) (xs : List Ex) :
    Up P (addL xs) (xs.length - 1) 0
      (fun e l => (∀ x, xs = [x] → e = x) ∧ (xs = [] → l.idxOf? (.const 0) = some e.node)) := by
  match xs with
  | [] => exact (Up.constant 0).post fun _ _ h => ⟨fun _ h' => by simp at h', fun _ => h⟩
  | [x] => exact Up.pure fun _ _ => ⟨fun _ h => by simp at h; exact h, fun h => by simp at h⟩
  | x :: y :: ys =>
    exact ((addFrom_up hP x (y :: ys)).cost_of (by simp) rfl).post fun _ _ _ =>
      ⟨fun _ h => by simp at h, fun h => by simp at h⟩

theorem registerEq_up (hP : Mono P) (B Rj ιj : Ex) (decs incs : List Ex) :
    Up P (Packed.registerEq B Rj ιj decs incs) (decs.length - 1 + (incs.length - 1) + 3) 3
      (fun φ l => Cost 1 1 φ ∧ ∀ x, incs = [x] → .mul B.node x.node ∈ l) := by
  apply Up.cost_of
  case h =>
    unfold Packed.registerEq
    up_norm
    up_run with_reducible refine addL_up' ?_ _
    all_goals refine ⟨⟨rfl, rfl⟩, fun x hx => ?_⟩
    all_goals obtain rfl := ‹∀ y, incs = [y] → _ = y› x hx
    all_goals exact mem_of_idxOf? (by assumption)
  all_goals omega

/-- The nodes `B·0` and `e + B·0` are present. -/
def ZPre (B e : ℕ) (l : List NatNode) : Prop :=
  ∃ z u, l.idxOf? (.const 0) = some z ∧ l.idxOf? (.mul B z) = some u ∧ NatNode.add e u ∈ l

/-- The right side of the atom `φ` is the node `e + B·0`. -/
def ZPost (B e : ℕ) (φ : NForm) (l : List NatNode) : Prop :=
  ∃ z u v, l.idxOf? (.const 0) = some z ∧ l.idxOf? (.mul B z) = some u ∧
    l.idxOf? (.add e u) = some v ∧ rhsNode φ = some v

theorem Mono.zPre (B e : ℕ) : Mono (ZPre B e) := ⟨fun l l' h ⟨z, u, h1, h2, h3⟩ =>
  ⟨z, u, (Mono.idxOf? _ _).mono l l' h h1, (Mono.idxOf? _ _).mono l l' h h2,
    (Mono.mem _).mono l l' h h3⟩⟩

theorem Mono.zPost (B e : ℕ) (φ : NForm) : Mono (ZPost B e φ) :=
  ⟨fun l l' h ⟨z, u, v, h1, h2, h3, h4⟩ =>
    ⟨z, u, v, (Mono.idxOf? _ _).mono l l' h h1, (Mono.idxOf? _ _).mono l l' h h2,
      (Mono.idxOf? _ _).mono l l' h h3, h4⟩⟩

theorem ZPost.zPre {B e : ℕ} {φ : NForm} {l : List NatNode} (h : ZPost B e φ l) : ZPre B e l :=
  let ⟨z, u, _, h1, h2, h3, _⟩ := h
  ⟨z, u, h1, h2, mem_of_idxOf? h3⟩

theorem stateEq_up (hP : Mono P) (B Si e : Ex) (ins : List Ex) :
    Up P (Packed.stateEq B Si e ins) (ins.length - 1 + 1) 1
      (fun φ l => Cost 1 1 φ ∧ (ins = [] → ZPost B.node e.node φ l)) := by
  apply Up.cost_of
  case h =>
    unfold Packed.stateEq
    up_norm
    up_run with_reducible refine addL_up' ?_ _
    all_goals refine ⟨⟨rfl, rfl⟩, fun hx => ⟨_, _, _, ‹_ = [] → _› hx, by assumption,
      by assumption, rfl⟩⟩
  all_goals rfl

theorem stateEq_up_a (hP : Mono P) (B Si e v w : Ex) (rest : List Ex)
    (h : ∀ l, P l → .add v.node w.node ∈ l) :
    Up P (Packed.stateEq B Si e (v :: w :: rest)) (rest.length + 1) 1 (fun φ _ => Cost 1 1 φ) := by
  refine Up.pre (P := fun l => P l ∧ .add v.node w.node ∈ l) ?_ fun l hl => ⟨hl, h l hl⟩
  apply Up.cost_of
  case h =>
    unfold Packed.stateEq
    up_norm
    up_run with_reducible refine addFrom_up ?_ _ _
    all_goals exact ⟨rfl, rfl⟩
  all_goals omega

theorem stateEq_up_b (hP : Mono P) (B Si e x : Ex) (h : ∀ l, P l → .mul B.node x.node ∈ l) :
    Up P (Packed.stateEq B Si e [x]) 1 0 (fun φ _ => Cost 1 1 φ) := by
  refine Up.pre (P := fun l => P l ∧ .mul B.node x.node ∈ l) ?_ fun l hl => ⟨hl, h l hl⟩
  apply Up.cost_of
  case h =>
    unfold Packed.stateEq
    up_norm
    up_run0
    all_goals exact ⟨rfl, rfl⟩
  all_goals rfl

theorem stateEq_up_c (hP : Mono P) (B Si e : Ex) (h : ∀ l, P l → ZPre B.node e.node l) :
    Up P (Packed.stateEq B Si e []) 0 0 (fun φ l => Cost 1 1 φ ∧ ZPost B.node e.node φ l) := by
  unfold Packed.stateEq
  simp only [addL.eq_1]
  up_norm
  apply Up.cost_of
  case h =>
    refine Up.bind hP (Up.constant 0) fun z => Up.bind (Mono.and hP (Mono.idxOf? _ _))
      (Up.node_hit (n := .mul B.node z.node) fun l hl => ?_) fun u => Up.bind
        (Mono.and (Mono.and hP (Mono.idxOf? _ _)) (Mono.idxOf? _ _))
        (Up.node_hit (n := .add e.node u) fun l hl => ?_) fun v => Up.pure fun l hl =>
          ⟨⟨rfl, rfl⟩, _, _, _, hl.1.1.2, hl.1.2, hl.2, rfl⟩
    · obtain ⟨z', u', h1, h2, -⟩ := h l hl.1
      rw [hl.2, Option.some.injEq] at h1
      exact h1 ▸ mem_of_idxOf? h2
    · obtain ⟨z', u', h1, h2, h3⟩ := h l hl.1.1
      rw [hl.1.2, Option.some.injEq] at h1
      subst h1
      rw [hl.2, Option.some.injEq] at h2
      exact h2 ▸ h3
  all_goals rfl

end ZInQ.Compiler.NodeBound
