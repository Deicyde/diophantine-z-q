import ZInQKernel.Compiler.NodeBound.Program67

/-!
# Node bounds of the compiled circuit, for every program

`compiled_bound`: for every program `p` with `m ≥ 1` instructions, `d` sub instructions,
`r + 1` registers and `k` inputs, the compiled circuit `𝒞_{p,k}` has at most `addBound p r k`
addition and `mulBound p r k` multiplication nodes. These are the sums of the bounds of the
items and of the encoding; the program enters through `m`, `d`, the item-6 and item-7 bounds
(`cost6`, `cost7A`, `cost7M`) and the number `nC7` of states other than `0` without
predecessors (whose atoms share their right side, so the encoding saves `nC7 - 1`
multiplications).
-/

namespace ZInQ.Compiler.NodeBound

open Natural Universal RM

variable {P : List NatNode → Prop}

theorem Up.of_pre_fact {α : Type} {m : NM α} {a b : ℕ} {Q : α → List NatNode → Prop} {p : Prop}
    (hp : ∀ l, P l → p) (h : p → Up P m a b Q) : Up P m a b Q :=
  ⟨fun s hs => (h (hp _ hs)).run s hs⟩

theorem freshN_up (hP : Mono P) (n : ℕ) :
    Up P (Packed.freshN n) 0 0 (fun S _ => S.length = n) := by
  induction n generalizing P with
  | zero => exact Up.pure fun _ _ => rfl
  | succ n ih =>
    simp only [Packed.freshN]
    exact (Up.bind hP Up.fresh fun h => Up.bind (Mono.and hP (Mono.const _))
      (ih (Mono.and hP (Mono.const _))) fun hs => Up.pure fun l hl => by
        simp [hl.2]).cost_of rfl rfl

/-- Repeats of right sides: every occurrence of `v` after the first is counted. -/
theorem countP_le_dupGo (v : ℕ) : ∀ (φs : List NForm) (seen : List ℕ),
    φs.countP (fun φ => rhsNode φ = some v) ≤ dupGo φs seen + if v ∈ seen then 0 else 1
  | [], _ => by simp
  | φ :: φs, seen => by
    cases h : rhsNode φ with
    | none =>
      have := countP_le_dupGo v φs seen
      simp only [List.countP_cons, h, dupGo, reduceCtorEq, decide_false, Bool.false_eq_true,
        ite_false]
      omega
    | some w =>
      have ih := countP_le_dupGo v φs (w :: seen)
      have e1 : (φ :: φs).countP (fun φ => rhsNode φ = some v) =
          φs.countP (fun φ => rhsNode φ = some v) + (if w = v then 1 else 0) := by
        simp [List.countP_cons, h]
      have e2 : dupGo (φ :: φs) seen = (if w ∈ seen then 1 else 0) + dupGo φs (w :: seen) := by
        simp [dupGo, h]
      rw [e1, e2]
      by_cases hw : w = v
      · subst hw
        simp only [List.mem_cons, true_or, ite_true, Nat.add_zero] at ih
        split_ifs <;> omega
      · simp only [List.mem_cons, Ne.symm hw, false_or] at ih
        simp only [hw, ite_false]
        split_ifs at * <;> omega

theorem dupGo_ge {L L7 : List NForm} {n v : ℕ}
    (h : n ≤ L7.countP fun φ => rhsNode φ = some v) : n - 1 ≤ dupGo (L ++ L7) [] := by
  have h1 := countP_le_dupGo v (L ++ L7) []
  rw [List.countP_append] at h1
  simp only [List.not_mem_nil, ite_false] at h1
  omega

/-! ### Items 1–7 -/

/-- Monotonicity side goals with quantified facts. -/
macro "mono_tac" : tactic => `(tactic| repeat' (first
  | up_mono
  | (with_reducible apply Mono.forall_mem)
  | (with_reducible apply Mono.forall')
  | (with_reducible apply Mono.pre7)
  | (with_reducible apply Mono.post7)
  | (intro _)))

/-- The additions of items 1–7. -/
def itemsA (p : Program) (r k : ℕ) : ℕ :=
  (4 + 2 * k) + (3 + (p.length - 1)) + (9 + (p.length - 1) * 8) + (42 + r * 41) +
    31 * p.subCount + cost6 p (r + 1) + cost7A (symIn p) (decPos 0 p) (List.range p.length) false

/-- The multiplications of items 1–7. -/
def itemsM (p : Program) (r : ℕ) : ℕ :=
  1 + 3 + (3 + (p.length - 1) * 3) + (13 + r * 13) + 9 * p.subCount + 3 * (r + 1) +
    cost7M (symIn p) (singles p (r + 1)) (List.range p.length) false

/-- The encoding costs and the number of the formulas of items 1–7. -/
def formA (p : Program) (r k : ℕ) : ℕ :=
  (3 + k) + 4 + (10 + (p.length - 1) * 10) + (47 + r * 47) + 37 * p.subCount + (r + 1) + p.length

def formM (p : Program) (r k : ℕ) : ℕ :=
  (3 + k) + 4 + (12 + (p.length - 1) * 12) + (56 + r * 56) + 44 * p.subCount + (r + 1) + p.length

def formN (p : Program) (r k : ℕ) : ℕ :=
  (5 + k) + 4 + (1 + (p.length - 1)) + (3 + r * 3) + 2 * p.subCount + (r + 1) + p.length

theorem packedFormulas_up (hP : Mono P) (p : Program) (r : ℕ) (a : List Ex)
    (zero one q c K B T F D x : Ex) (R N xs : List Ex) (hxs : xs.length + 1 = p.length) :
    Up P (Packed.packedFormulas p (r + 1) a zero one q c K B T F D R N (x :: xs))
      (itemsA p r a.length) (itemsM p r)
      (fun φs _ => CostL (formA p r a.length) (formM p r a.length) (formN p r a.length) φs ∧
        nC7 (symIn p) (List.range p.length) - 1 ≤ dupGo φs []) := by
  unfold Packed.packedFormulas
  simp only [Packed.appendM, NM.bind_assoc', NM.pure_bind']
  apply Up.cost_of
  case h =>
    refine Up.bind hP (items1_up hP p a zero q c K B T) fun l1 =>
      Up.bind ?_ (items2_up ?_ zero one K B T F D (x :: xs)) fun l2 =>
      Up.bind ?_ (items3_up ?_ F x xs) fun l3 =>
      Up.bind ?_ (items4_up ?_ r zero K D T F R N ?_) fun l4 =>
      Up.bind ?_ (subBranches_up zero (x :: xs) N p 0 ?_) fun sb =>
      Up.of_pre_fact (p := sb.2.map Prod.fst = decPos 0 p) ?_ fun hvw =>
      Up.bind ?_ (items6_up (r := r + 1) (a := a) (B := B) (R := R) hvw ?_) fun l6 =>
      Up.bind ?_ (items7_up (r := r + 1) (one := one) hvw ?_ ?_) fun l7 =>
      Up.pure fun l hl => ?_
    all_goals try first
      | mono_tac; done
      | up_present
    · intro l h
      casesm* _ ∧ _
      exact ⟨by assumption, by assumption⟩
    · casesm* _ ∧ _, CostL _ _ _ _
      refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
      · simp only [encAL_append, *, formA]; omega
      · simp only [encML_append, *, formM]; omega
      · simp only [List.length_append, *, formN]; omega
      · obtain h0 | ⟨v, z, u, -, -, -, hc⟩ := ‹Post7 _ _ _ _ _›
        · rw [h0]; exact Nat.zero_le _
        · simp only [← List.append_assoc]
          exact dupGo_ge hc
  all_goals simp only [itemsA, itemsM, List.length_cons]; omega

/-! ### The compiled circuit -/

/-- The bound on the addition nodes of `𝒞_{p,k}` with `r + 1` registers. -/
def addBound (p : Program) (r k : ℕ) : ℕ := itemsA p r k + (formA p r k + (formN p r k - 1))

/-- The bound on the multiplication nodes of `𝒞_{p,k}` with `r + 1` registers. -/
def mulBound (p : Program) (r k : ℕ) : ℕ :=
  itemsM p r + (formM p r k - (nC7 (symIn p) (List.range p.length) - 1) + formN p r k)

theorem construction_encode_up (p : Program) (r k : ℕ) (hm : 1 ≤ p.length) :
    Up (fun _ => True) (Packed.construction p (r + 1) k >>= fun φ => φ.encode Syntax.ExPoly.empty)
      (addBound p r k) (mulBound p r k) (fun _ _ => True) := by
  have hT : Mono fun _ : List NatNode => True := Mono.const _
  have hk : (inputs k).length = k := by simp [inputs]
  unfold Packed.construction
  simp only [NM.bind_assoc', NM.pure_bind']
  refine Up.weaken (Up.bind hT (Up.constant 0) fun zero => Up.bind ?_ (Up.constant 1) fun one =>
    Up.bind ?_ Up.fresh fun q => Up.bind ?_ Up.fresh fun c => Up.bind ?_ Up.fresh fun K =>
    Up.bind ?_ Up.fresh fun B => Up.bind ?_ Up.fresh fun T => Up.bind ?_ Up.fresh fun F =>
    Up.bind ?_ Up.fresh fun D => Up.bind ?_ (freshN_up ?_ (r + 1)) fun R =>
    Up.bind ?_ (freshN_up ?_ (r + 1)) fun N => Up.bind ?_ (freshN_up ?_ p.length) fun S =>
    Up.of_pre_fact (a := addBound p r k) (b := mulBound p r k) (p := S.length = p.length)
      (fun _ h => h.2) fun hS => ?_) (by simp) (by simp)
  all_goals try ((repeat' (first | exact hT | apply Mono.and | apply Mono.const |
    apply Mono.idxOf?)); done)
  obtain ⟨x, xs, rfl⟩ : ∃ x xs, S = x :: xs := by
    cases S with
    | nil => simp at hS; omega
    | cons x xs => exact ⟨x, xs, rfl⟩
  have hxs : xs.length + 1 = p.length := by simpa using hS
  refine Up.weaken (Up.bind ?_ (packedFormulas_up ?_ p r (inputs k) zero one q c K B T F D x R N
    xs hxs) fun φs => Up.of_pre_fact (a := formA p r k + (formN p r k - 1))
      (b := formM p r k - (nC7 (symIn p) (List.range p.length) - 1) + formN p r k)
      (p := CostL (formA p r k) (formM p r k) (formN p r k) φs ∧
        nC7 (symIn p) (List.range p.length) - 1 ≤ dupGo φs []) (fun _ h => by rw [hk] at h; exact h.2)
      fun ⟨⟨ha, hb, hn⟩, hd⟩ => (encode_and_up _ ?_ φs).weaken (by rw [ha, hn])
        (by rw [hb, hn]; omega)) (by simp only [addBound, hk]; omega)
        (by simp only [mulBound]; omega)
  all_goals repeat' (first | exact hT | apply Mono.and | apply Mono.const | apply Mono.idxOf?)

theorem countKind_init (κ : NodeKind) (hκ : κ ≠ .var) (k : ℕ) :
    countKind κ (State.init k).nodes = 0 := by
  simp only [State.init, countKind, List.countP_eq_zero, List.mem_map, List.mem_range]
  rintro _ ⟨i, -, rfl⟩
  simp [nodeKind, Ne.symm hκ]

/-- **Node bounds of the compiled circuit**, for every program with at least one instruction. -/
theorem compiled_bound (p : Program) (r k : ℕ) (hm : 1 ≤ p.length) :
    countKind .add (Packed.compiled p (r + 1) k).nodes ≤ addBound p r k ∧
      countKind .mul (Packed.compiled p (r + 1) k).nodes ≤ mulBound p r k := by
  obtain ⟨-, h1, h2, -⟩ := (construction_encode_up p r k hm).run (State.init k) trivial
  rw [NM.bind_apply] at h1 h2
  rw [Packed.compiled, NM.toCircuit_nodes]
  have ha := countKind_init .add (by decide) k
  have hb := countKind_init .mul (by decide) k
  simp only [cA, cM] at h1 h2
  exact ⟨by omega, by omega⟩

end ZInQ.Compiler.NodeBound
