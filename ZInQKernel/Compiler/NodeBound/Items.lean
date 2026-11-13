import ZInQKernel.Compiler.NodeBound.Macros
import ZInQKernel.Compiler.Circuits.Packed.Construction

/-!
# Node bounds of items 1–5 of the packed-history construction

For every program `p` (with `m` instructions, `d` of them sub instructions), `r ≥ 1` registers and
`k` inputs:

| item | additions | multiplications | formulas (encoding costs) |
|---|---|---|---|
| 1 | `4 + 2k` | `1` | `(3 + k, 3 + k)` |
| 2 | `3 + (m - 1)` | `3` | `(4, 4)` |
| 3 | `9 + 8 (m - 1)` (`m ≥ 1`) | `3m` | `(10m, 12m)` |
| 4 | `42 + 41 (r - 1)` | `13r` | `(47r, 56r)` |
| 5 | `31d` | `9d` | `(37d, 44d)` |

The program-independent repeats subtracted here: `F + 1` in all masks of item 3 but the first,
`D + 1` in all register masks of item 4 but the first, `K·F` in every register of item 4 (it is
built by item 2), and the two re-sums of every `bitAnd`.
-/

namespace ZInQ.Compiler.NodeBound

open Natural Universal Packed RM

variable {P : List NatNode → Prop}

theorem addFrom_up (hP : Mono P) (acc : Ex) (ys : List Ex) :
    Up P (addFrom acc ys) ys.length 0 (fun _ _ => True) := by
  induction ys generalizing acc P with
  | nil => exact Up.pure fun _ _ => trivial
  | cons y ys ih =>
    simp only [addFrom]
    exact (Up.bind hP (Up.node_add acc.node y.node) fun i =>
      ih (Mono.and hP (Mono.idxOf? _ _)) ⟨i, _⟩).cost_of (by simp; omega) rfl

theorem mulFrom_up (hP : Mono P) (acc : Ex) (ys : List Ex) :
    Up P (mulFrom acc ys) 0 ys.length (fun _ _ => True) := by
  induction ys generalizing acc P with
  | nil => exact Up.pure fun _ _ => trivial
  | cons y ys ih =>
    simp only [mulFrom]
    exact (Up.bind hP (Up.node_mul acc.node y.node) fun i =>
      ih (Mono.and hP (Mono.idxOf? _ _)) ⟨i, _⟩).cost_of rfl (by simp; omega)

theorem addL_up (hP : Mono P) (xs : List Ex) :
    Up P (addL xs) (xs.length - 1) 0 (fun _ _ => True) := by
  cases xs with
  | nil => exact (Up.constant 0).post fun _ _ _ => trivial
  | cons x xs => exact (addFrom_up hP x xs).cost_of (by simp) rfl

theorem mulL_up (hP : Mono P) (xs : List Ex) :
    Up P (mulL xs) 0 (xs.length - 1) (fun _ _ => True) := by
  cases xs with
  | nil => exact (Up.constant 1).post fun _ _ _ => trivial
  | cons x xs => exact (mulFrom_up hP x xs).cost_of rfl (by simp)

/-- A list of constructions with uniform bounds, under any stronger monotone precondition. -/
theorem seqM_up {a b ca cb : ℕ} (L : List (NM NForm)) (hP : Mono P)
    (h : ∀ m ∈ L, ∀ P' : List NatNode → Prop, Mono P' → (∀ l, P' l → P l) →
      Up P' m a b (fun φ _ => Cost ca cb φ)) :
    Up P (seqM L) (L.length * a) (L.length * b)
      (fun φs _ => CostL (L.length * ca) (L.length * cb) L.length φs) := by
  induction L generalizing P with
  | nil =>
    exact (Up.pure (Q := fun φs _ => CostL _ _ _ φs) fun _ _ =>
      ⟨by simp [encAL], by simp [encML], rfl⟩).cost_of (by simp) (by simp)
  | cons m ms ih =>
    simp only [seqM]
    refine (Up.bind hP (h m (List.mem_cons_self ..) P hP fun _ h => h) fun φ =>
      Up.bind (Mono.and hP (Mono.const _)) (ih (Mono.and hP (Mono.const _))
        fun m' hm' P' hP' hle => h m' (List.mem_cons_of_mem _ hm') P' hP'
          fun l hl => (hle l hl).1) fun φs => Up.pure fun l hl => ?_).cost_of ?_ ?_
    · obtain ⟨⟨-, h1, h2⟩, h3, h4, h5⟩ := hl
      exact ⟨by simp only [encAL, h1, h3, List.length_cons]; ring,
        by simp only [encML, h2, h4, List.length_cons]; ring, by simp [h5]⟩
    · simp only [List.length_cons]; ring
    · simp only [List.length_cons]; ring

/-- Concatenated lists of constructions with uniform bounds. -/
theorem seqConcat_up {a b ca cb cn : ℕ} (L : List (NM (List NForm))) (hP : Mono P)
    (h : ∀ m ∈ L, ∀ P' : List NatNode → Prop, Mono P' → (∀ l, P' l → P l) →
      Up P' m a b (fun φs _ => CostL ca cb cn φs)) :
    Up P (seqConcat L) (L.length * a) (L.length * b)
      (fun φs _ => CostL (L.length * ca) (L.length * cb) (L.length * cn) φs) := by
  induction L generalizing P with
  | nil =>
    exact (Up.pure (Q := fun φs _ => CostL _ _ _ φs) fun _ _ =>
      ⟨by simp [encAL], by simp [encML], by simp⟩).cost_of (by simp) (by simp)
  | cons m ms ih =>
    simp only [seqConcat]
    refine (Up.bind hP (h m (List.mem_cons_self ..) P hP fun _ h => h) fun φ =>
      Up.bind (Mono.and hP (Mono.const _)) (ih (Mono.and hP (Mono.const _))
        fun m' hm' P' hP' hle => h m' (List.mem_cons_of_mem _ hm') P' hP'
          fun l hl => (hle l hl).1) fun φs => Up.pure fun l hl => ?_).cost_of ?_ ?_
    · obtain ⟨⟨-, h1, h2, h5⟩, h3, h4, h6⟩ := hl
      exact ⟨by rw [encAL_append, h1, h3, List.length_cons]; ring,
        by rw [encML_append, h2, h4, List.length_cons]; ring,
        by rw [List.length_append, h5, h6, List.length_cons]; ring⟩
    · simp only [List.length_cons]; ring
    · simp only [List.length_cons]; ring

/-! ### Items 1–4 -/

theorem seqM_lt_up (hP : Mono P) (a : List Ex) (K : Ex) :
    Up P (seqM (a.map fun ai => Natural.lt ai K)) (a.length * 2) (a.length * 0)
      (fun φs _ => CostL (a.length * 1) (a.length * 1) a.length φs) := by
  have h := seqM_up (a := 2) (b := 0) (ca := 1) (cb := 1) (a.map fun ai => Natural.lt ai K) hP
    fun m hm P' hP' _ => by
      obtain ⟨ai, -, rfl⟩ := List.mem_map.1 hm
      exact lt_up hP' ai K
  simpa only [List.length_map] using h

theorem items1_up (hP : Mono P) (p : Program) (a : List Ex) (zero q c K B T : Ex) :
    Up P (items1 p a zero q c K B T) (4 + 2 * a.length) 1
      (fun φs _ => CostL (3 + a.length) (3 + a.length) (5 + a.length) φs) := by
  apply Up.cost_of
  case h =>
    unfold items1
    simp only [List.cons_append, List.nil_append]
    up_norm
    up_run first
      | up_lt
      | with_reducible refine seqM_lt_up ?_ _ _
    all_goals exact ⟨by simp only [encAL, encA, *]; omega, by simp only [encML, encM, *]; omega,
      by simp only [List.length_cons, *]; omega⟩
  all_goals omega

theorem items2_up (hP : Mono P) (zero one K B T F D : Ex) (S : List Ex) :
    Up P (items2 zero one K B T F D S) (3 + (S.length - 1)) 3
      (fun φs l => CostL 4 4 4 φs ∧ .mul K.node F.node ∈ l) := by
  apply Up.weaken
  case h =>
    unfold items2
    up_norm
    up_run with_reducible refine addL_up ?_ _
    all_goals exact ⟨⟨rfl, rfl, rfl⟩, mem_of_idxOf? (by assumption)⟩
  all_goals omega

/-- One step through `mask`. -/
macro "up_mask" : tactic => `(tactic| first
  | (with_reducible refine mask_up_succ ?_ _ _ ?_; rotate_left; up_present)
  | with_reducible refine mask_up ?_ _ _)

theorem items3_up (hP : Mono P) (F x : Ex) (xs : List Ex) :
    Up P (items3 F (x :: xs)) (9 + xs.length * 8) (3 + xs.length * 3)
      (fun φs _ => CostL (10 + xs.length * 10) (12 + xs.length * 12) (1 + xs.length) φs) := by
  unfold items3
  simp only [List.map_cons, seqM]
  have h := seqM_up (a := 8) (b := 3) (ca := 10) (cb := 12) (P := fun l => P l ∧ HasSucc F.node l)
    (xs.map fun x => mask .hierarchical x F) (Mono.and hP (Mono.hasSucc _))
    fun m hm P' hP' hle => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hm
      exact (mask_up_succ hP' y F fun l hl => (hle l hl).2).post fun _ _ h => h.1
  simp only [List.length_map] at h
  refine (Up.bind hP (mask_up hP x F) fun φ => Up.bind
    (Mono.and hP (Mono.and (Mono.const _) (Mono.hasSucc _)))
    (h.pre fun l hl => ⟨hl.1, hl.2.2⟩) fun φs => Up.pure fun l hl => ?_).cost_of (by omega) (by omega)
  obtain ⟨⟨-, ⟨h1, h2⟩, -⟩, h3, h4, h5⟩ := hl
  exact ⟨by simp only [encAL, h1, h3], by simp only [encML, h2, h4],
    by simp only [List.length_cons, h5]; omega⟩

theorem registerMasks_up (hP : Mono P) (K D T F Rj Nj : Ex)
    (hKF : ∀ l, P l → .mul K.node F.node ∈ l) :
    Up P (registerMasks K D T F Rj Nj) 42 13 (fun φs l => CostL 47 56 3 φs ∧ HasSucc D.node l) := by
  refine Up.pre (P := fun l => P l ∧ .mul K.node F.node ∈ l) ?_ fun l hl => ⟨hl, hKF l hl⟩
  apply Up.cost_of
  case h =>
    unfold registerMasks
    up_norm
    up_run first | up_lt | up_mask | with_reducible refine bitAnd_up ?_ _ _ _
    all_goals exact ⟨by up_costs, by assumption⟩
  all_goals rfl

theorem registerMasks_up_succ (hP : Mono P) (K D T F Rj Nj : Ex)
    (hKF : ∀ l, P l → .mul K.node F.node ∈ l) (hD : ∀ l, P l → HasSucc D.node l) :
    Up P (registerMasks K D T F Rj Nj) 41 13 (fun φs l => CostL 47 56 3 φs ∧ HasSucc D.node l) := by
  refine Up.pre (P := fun l => (P l ∧ .mul K.node F.node ∈ l) ∧ HasSucc D.node l) ?_
    fun l hl => ⟨⟨hl, hKF l hl⟩, hD l hl⟩
  apply Up.cost_of
  case h =>
    unfold registerMasks
    up_norm
    up_run first | up_lt | up_mask | with_reducible refine bitAnd_up ?_ _ _ _
    all_goals exact ⟨by up_costs, by assumption⟩
  all_goals rfl

theorem items4_up (hP : Mono P) (r : ℕ) (zero K D T F : Ex) (R N : List Ex)
    (hKF : ∀ l, P l → .mul K.node F.node ∈ l) :
    Up P (items4 (r + 1) zero K D T F R N) (42 + r * 41) (13 + r * 13)
      (fun φs _ => CostL (47 + r * 47) (56 + r * 56) (3 + r * 3) φs) := by
  unfold items4
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [seqConcat]
  have h := seqConcat_up (a := 41) (b := 13) (ca := 47) (cb := 56) (cn := 3)
    (P := fun l => P l ∧ HasSucc D.node l)
    ((List.range r).map ((fun j => registerMasks K D T F (R.getD j zero) (N.getD j zero)) ∘
      Nat.succ)) (Mono.and hP (Mono.hasSucc _))
    fun m hm P' hP' hle => by
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hm
      exact (registerMasks_up_succ hP' _ _ _ _ _ _ (fun l hl => hKF l (hle l hl).1)
        fun l hl => (hle l hl).2).post fun _ _ h => h.1
  simp only [List.length_map, List.length_range] at h
  refine (Up.bind hP (registerMasks_up hP K D T F _ _ hKF) fun φ => Up.bind
    (Mono.and hP (Mono.and (Mono.const _) (Mono.hasSucc _))) (h.pre fun l hl => ⟨hl.1, hl.2.2⟩) fun φs =>
      Up.pure fun l hl => ?_).cost_of (by omega) (by omega)
  obtain ⟨⟨-, ⟨h1, h2, h5⟩, -⟩, h3, h4, h6⟩ := hl
  exact ⟨by rw [encAL_append, h1, h3], by rw [encML_append, h2, h4],
    by rw [List.length_append, h5, h6]⟩

/-! ### Item 5 -/

/-- The positions of the sub instructions of `p`, counted from `i`. -/
def decPos : ℕ → List Instr → List ℕ
  | _, [] => []
  | i, .dec _ _ _ :: rest => i :: decPos (i + 1) rest
  | i, _ :: rest => decPos (i + 1) rest

theorem subBranches_up (zero : Ex) (S N : List Ex) (p : Program) :
    ∀ {P : List NatNode → Prop} (i : ℕ), Mono P →
    Up P (subBranches zero S N i p) (31 * p.subCount) (9 * p.subCount)
      (fun r l => CostL (37 * p.subCount) (44 * p.subCount) (2 * p.subCount) r.1 ∧
        (∀ e ∈ r.2, .add e.2.1.node e.2.2.node ∈ l) ∧ r.2.map Prod.fst = decPos i p) := by
  induction p with
  | nil => exact fun i hP => Up.pure fun _ _ => ⟨⟨rfl, rfl, rfl⟩, by simp, rfl⟩
  | cons ins rest ih =>
    intro P i hP
    cases ins with
    | dec j x y =>
      apply Up.cost_of
      case h =>
        unfold subBranches
        up_norm
        up_run first | with_reducible refine bitAnd_up ?_ _ _ _ | with_reducible refine ih _ ?_
        all_goals refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
        · simp only [encAL_append, encAL, encA, *]
          simp [Program.subCount, List.countP_cons, Instr.isDec]; omega
        · simp only [encML_append, encML, encM, *]
          simp [Program.subCount, List.countP_cons, Instr.isDec]; omega
        · simp only [List.length_append, List.length_cons, List.length_nil, *]
          simp [Program.subCount, List.countP_cons, Instr.isDec]; omega
        · intro e he
          rcases List.mem_cons.1 he with rfl | he
          · exact mem_of_idxOf? (by assumption)
          · solve_by_elim
        · simp only [List.map_cons, decPos, *]
      all_goals simp [Program.subCount, List.countP_cons, Instr.isDec]; omega
    | inc j x =>
      simpa [subBranches, Program.subCount, List.countP_cons, Instr.isDec, decPos] using
        ih (i + 1) hP
    | halt =>
      simpa [subBranches, Program.subCount, List.countP_cons, Instr.isDec, decPos] using
        ih (i + 1) hP

end ZInQ.Compiler.NodeBound
