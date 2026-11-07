import ZInQKernel.Compiler.NodeBound.Items67
import ZInQKernel.Compiler.NodeCheck.Fast

/-!
# Node bounds of items 6 and 7, for every program

The handles of items 6 and 7 are read symbolically: `S_i`, `V_i`, `W_i` get the codes `3i + 3`,
`3i + 4`, `3i + 5` and the constant zero the code `0` (`sCodes`, `vwCodes`). The handle lists of
the construction are the images of the symbolic handle lists (`symInc`, `symDec`, `symIn`) under
the reading `codeEx` of codes as expressions (`inc_corr`, `dec_corr`, `in_corr`). The bounds of
items 6 and 7 (`cost6`, `cost7A`, `cost7M`) and the number `nC7` of states other than `0` without
predecessors are functions of the symbolic handle lists. Equal codes are read as equal
expressions; no distinctness of the codes is used.
-/

namespace ZInQ.Compiler.NodeBound

open Natural Universal RM

/-! ### Symbolic handles -/

/-- The codes of `S_0, …, S_{m-1}`. -/
def sCodes (m : ℕ) : List ℕ := (List.range m).map fun i => 3 * i + 3

/-- The symbolic branch histories: `(i, code V_i, code W_i)` for the sub instructions. -/
def vwCodes (p : Program) : List (ℕ × ℕ × ℕ) := (decPos 0 p).map fun i => (i, 3 * i + 4, 3 * i + 5)

/-- The symbolic summands of `A_j`. -/
def symInc (p : Program) (j : ℕ) : List ℕ := NodeCheck.incHandles p 0 (sCodes p.length) j

/-- The symbolic summands of `C_j`. -/
def symDec (p : Program) (j : ℕ) : List ℕ := NodeCheck.decHandles p 0 (vwCodes p) j

/-- The symbolic summands of `I_i`. -/
def symIn (p : Program) (i : ℕ) : List ℕ := NodeCheck.inHandles p 0 (sCodes p.length) (vwCodes p) i

/-- The expression of a code. -/
def codeEx (zero : Ex) (S : List Ex) (vw : List (ℕ × Ex × Ex)) (c : ℕ) : Ex :=
  if c = 0 then zero
  else if c % 3 = 0 then S.getD (c / 3 - 1) zero
  else if c % 3 = 1 then (Packed.lookupVW zero vw ((c - 4) / 3)).1
  else (Packed.lookupVW zero vw ((c - 5) / 3)).2

section Codes

variable {zero : Ex} {S : List Ex} {vw : List (ℕ × Ex × Ex)}

theorem codeEx_s (i : ℕ) : codeEx zero S vw (3 * i + 3) = S.getD i zero := by
  unfold codeEx
  split_ifs <;> first | omega | contradiction | rw [show (3 * i + 3) / 3 - 1 = i by omega]

theorem codeEx_v (i : ℕ) : codeEx zero S vw (3 * i + 4) = (Packed.lookupVW zero vw i).1 := by
  unfold codeEx
  split_ifs <;> first | omega | contradiction | rw [show (3 * i + 4 - 4) / 3 = i by omega]

theorem codeEx_w (i : ℕ) : codeEx zero S vw (3 * i + 5) = (Packed.lookupVW zero vw i).2 := by
  unfold codeEx
  split_ifs <;> first | omega | contradiction | rw [show (3 * i + 5 - 5) / 3 = i by omega]

theorem codeEx_zero : codeEx zero S vw 0 = zero := by simp [codeEx]

theorem getD_sCodes {m i : ℕ} (hi : i < m) : (sCodes m).getD i 0 = 3 * i + 3 := by
  simp [sCodes, hi]

theorem find?_map_pair (L : List ℕ) (g : ℕ → ℕ × ℕ) (i : ℕ) :
    ((L.map fun i' => (i', g i')).find? fun e => e.1 == i).map (·.2) =
      if i ∈ L then some (g i) else none := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.find?_cons]
    by_cases h : a = i
    · subst h; simp
    · have h' : ((a, g a).1 == i) = false := by simpa using h
      rw [h']
      dsimp only
      rw [ih]
      simp [List.mem_cons, Ne.symm h]

theorem symLookup (p : Program) (i : ℕ) :
    NodeCheck.lookupVW 0 (vwCodes p) i = if i ∈ decPos 0 p then (3 * i + 4, 3 * i + 5) else (0, 0) := by
  unfold NodeCheck.lookupVW vwCodes
  rw [find?_map_pair]
  split_ifs <;> rfl

theorem realLookup_of_not_mem {i : ℕ} (hi : i ∉ vw.map Prod.fst) :
    Packed.lookupVW zero vw i = (zero, zero) := by
  unfold Packed.lookupVW
  rw [List.find?_eq_none.2 fun e he h => hi (List.mem_map.2 ⟨e, he, by simpa using h⟩)]
  rfl

theorem realLookup_mem {i : ℕ} (hi : i ∈ vw.map Prod.fst) :
    ∃ e ∈ vw, Packed.lookupVW zero vw i = e.2 := by
  unfold Packed.lookupVW
  cases h : vw.find? fun e => e.1 == i with
  | none =>
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hi
    have := List.find?_eq_none.1 h e he
    simp at this
  | some e => exact ⟨e, List.mem_of_find?_eq_some h, rfl⟩

theorem codeEx_lookup {p : Program} (hvw : vw.map Prod.fst = decPos 0 p) (i : ℕ) :
    (codeEx zero S vw (NodeCheck.lookupVW 0 (vwCodes p) i).1,
      codeEx zero S vw (NodeCheck.lookupVW 0 (vwCodes p) i).2) = Packed.lookupVW zero vw i := by
  rw [symLookup]
  split_ifs with h
  · simp only [codeEx_v, codeEx_w]
  · simp only [codeEx_zero]
    rw [realLookup_of_not_mem (by rwa [hvw])]

theorem inc_corr (p : Program) (j : ℕ) :
    Packed.incHandles p zero S j = (symInc p j).map (codeEx zero S vw) := by
  unfold Packed.incHandles symInc NodeCheck.incHandles
  rw [List.map_map]
  refine List.map_congr_left fun i hi => ?_
  have : i < p.length := List.mem_range.1 (List.mem_filter.1 hi).1
  simp only [Function.comp, getD_sCodes this, codeEx_s]

theorem dec_corr {p : Program} (hvw : vw.map Prod.fst = decPos 0 p) (j : ℕ) :
    Packed.decHandles p zero vw j = (symDec p j).map (codeEx zero S vw) := by
  unfold Packed.decHandles symDec NodeCheck.decHandles
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  exact (congrArg Prod.fst (codeEx_lookup (zero := zero) (S := S) hvw i)).symm

theorem in_corr {p : Program} (hvw : vw.map Prod.fst = decPos 0 p) (i : ℕ) :
    Packed.inHandles p zero S vw i = (symIn p i).map (codeEx zero S vw) := by
  unfold Packed.inHandles symIn NodeCheck.inHandles
  rw [List.map_flatMap]
  refine List.flatMap_congr fun i' hi' => ?_
  have h1 : i' < p.length := List.mem_range.1 hi'
  have h2 := congrArg Prod.fst (codeEx_lookup (zero := zero) (S := S) hvw i')
  have h3 := congrArg Prod.snd (codeEx_lookup (zero := zero) (S := S) hvw i')
  simp only at h2 h3
  rw [getD_sCodes h1]
  split_ifs <;> simp only [List.map_append, List.map_cons, List.map_nil, codeEx_s, h2, h3,
    List.nil_append, List.append_nil]

end Codes

variable {P : List NatNode → Prop}

/-! ### Item 6 -/

/-- A list of formula constructions with per-element bounds and postconditions. -/
theorem seqM_up_idx {β : Type} (L : List β) (f : β → NM NForm) (ca cb : β → ℕ)
    (Post : β → List NatNode → Prop) (hPost : ∀ j, Mono (Post j)) (hP : Mono P)
    (h : ∀ j ∈ L, ∀ P' : List NatNode → Prop, Mono P' → (∀ l, P' l → P l) →
      Up P' (f j) (ca j) (cb j) (fun φ l => Cost 1 1 φ ∧ Post j l)) :
    Up P (seqM (L.map f)) (L.map ca).sum (L.map cb).sum
      (fun φs l => CostL L.length L.length L.length φs ∧ ∀ j ∈ L, Post j l) := by
  induction L generalizing P with
  | nil => exact Up.pure fun _ _ => ⟨⟨rfl, rfl, rfl⟩, fun _ h => absurd h List.not_mem_nil⟩
  | cons j L ih =>
    simp only [List.map_cons, seqM]
    refine (Up.bind hP (h j (List.mem_cons_self ..) P hP fun _ h => h) fun φ =>
      Up.bind (Mono.and hP (Mono.and (Mono.const _) (hPost j))) (ih (Mono.and hP
        (Mono.and (Mono.const _) (hPost j))) fun j' hj' P' hP' hle =>
          h j' (List.mem_cons_of_mem _ hj') P' hP' fun l hl => (hle l hl).1) fun φs =>
        Up.pure fun l hl => ?_).cost_of (by simp) (by simp)
    obtain ⟨⟨-, ⟨h1, h2⟩, h3⟩, ⟨h4, h5, h6⟩, h7⟩ := hl
    refine ⟨⟨by simp only [encAL, h1, h4, List.length_cons]; omega,
      by simp only [encML, h2, h5, List.length_cons]; omega, by simp [h6]⟩, fun j' hj' => ?_⟩
    rcases List.mem_cons.1 hj' with rfl | hj'
    · exact h3
    · exact h7 j' hj'

/-- The bound of item 6: `(|C_j| - 1) + (|A_j| - 1) + 3` additions for every register. -/
def cost6 (p : Program) (r : ℕ) : ℕ :=
  ((List.range r).map fun j => (symDec p j).length - 1 + ((symInc p j).length - 1) + 3).sum

theorem items6_up {p : Program} {r : ℕ} {a : List Ex} {zero B : Ex} {R S : List Ex}
    {vw : List (ℕ × Ex × Ex)} (hvw : vw.map Prod.fst = decPos 0 p) (hP : Mono P) :
    Up P (Packed.items6 p r a zero B R S vw) (cost6 p r) (3 * r)
      (fun φs l => CostL r r r φs ∧ ∀ j ∈ List.range r, ∀ x,
        Packed.incHandles p zero S j = [x] → .mul B.node x.node ∈ l) := by
  have h := seqM_up_idx (P := P) (List.range r) (fun j => Packed.registerEq B (R.getD j zero)
      (a.getD j zero) (Packed.decHandles p zero vw j) (Packed.incHandles p zero S j))
    (fun j => (symDec p j).length - 1 + ((symInc p j).length - 1) + 3) (fun _ => 3)
    (fun j l => ∀ x, Packed.incHandles p zero S j = [x] → .mul B.node x.node ∈ l)
    (fun j => Mono.forall' fun x => Mono.imp _ (Mono.mem _)) hP fun j _ P' hP' _ => by
      have := registerEq_up hP' B (R.getD j zero) (a.getD j zero) (Packed.decHandles p zero vw j)
        (Packed.incHandles p zero S j)
      rw [dec_corr (S := S) hvw, inc_corr (vw := vw), List.length_map, List.length_map] at this
      rw [inc_corr (vw := vw), dec_corr (S := S) hvw]
      exact this
  simp only [List.length_range, List.map_const', List.sum_replicate, smul_eq_mul] at h
  unfold Packed.items6 cost6
  exact h.cost_of rfl (Nat.mul_comm _ _)

/-! ### Item 7 -/

/-- The symbolic summands start with `V_i, W_i` of a sub instruction `i` (listed in `dp`). -/
def isA7 (dp : List ℕ) : List ℕ → Bool
  | c1 :: c2 :: _ => Nat.ble 4 c1 && c1 % 3 == 1 && c2 == c1 + 1 && dp.contains ((c1 - 4) / 3)
  | _ => false

/-- The symbolic summands are a single code of `sing`. -/
def isB7 (sing : List ℕ) : List ℕ → Bool
  | [c1] => sing.contains c1
  | _ => false

/-- State `i ≠ 0` has no predecessors. -/
def isC7 (i : ℕ) (c : List ℕ) : Bool := c.isEmpty && !(i == 0)

/-- The additions of item 7 for state `i` with symbolic summands `c`. -/
def step7A (dp : List ℕ) (i : ℕ) (c : List ℕ) (seen : Bool) : ℕ :=
  if isC7 i c then (if seen then 0 else 1) else c.length - 1 + 1 - (if isA7 dp c then 1 else 0)

/-- The multiplications of item 7 for state `i` with symbolic summands `c`. -/
def step7M (sing : List ℕ) (i : ℕ) (c : List ℕ) (seen : Bool) : ℕ :=
  if isC7 i c then (if seen then 0 else 1) else 1 - (if isB7 sing c then 1 else 0)

/-- The additions of item 7 for the states of `L` (`seen`: a state other than `0` without
predecessors came before). -/
def cost7A (insF : ℕ → List ℕ) (dp : List ℕ) : List ℕ → Bool → ℕ
  | [], _ => 0
  | i :: L, seen => step7A dp i (insF i) seen + cost7A insF dp L (seen || isC7 i (insF i))

/-- The multiplications of item 7 for the states of `L`. -/
def cost7M (insF : ℕ → List ℕ) (sing : List ℕ) : List ℕ → Bool → ℕ
  | [], _ => 0
  | i :: L, seen => step7M sing i (insF i) seen + cost7M insF sing L (seen || isC7 i (insF i))

/-- The number of states of `L` other than `0` without predecessors. -/
def nC7 (insF : ℕ → List ℕ) : List ℕ → ℕ
  | [] => 0
  | i :: L => (if isC7 i (insF i) then 1 else 0) + nC7 insF L

/-- The codes `c` with `A_j = c` for some register `j < r`. -/
def singles (p : Program) (r : ℕ) : List ℕ :=
  (List.range r).filterMap fun j =>
    match symInc p j with
    | [c] => some c
    | _ => none

theorem isA7_sound {dp c : List ℕ} (h : isA7 dp c = true) :
    ∃ i rest, c = (3 * i + 4) :: (3 * i + 5) :: rest ∧ i ∈ dp := by
  match c, h with
  | c1 :: c2 :: rest, h =>
    simp only [isA7, Bool.and_eq_true, Nat.ble_eq, beq_iff_eq, List.contains_iff_mem] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨q, rfl⟩ : ∃ q, c1 = 3 * q + 4 := ⟨(c1 - 4) / 3, by omega⟩
    have hq : (3 * q + 4 - 4) / 3 = q := by omega
    rw [hq] at h4
    exact ⟨q, rest, by rw [h3, show 3 * q + 4 + 1 = 3 * q + 5 by omega], h4⟩

theorem isB7_sound {p : Program} {r : ℕ} {c : List ℕ} (h : isB7 (singles p r) c = true) :
    ∃ c1, c = [c1] ∧ ∃ j < r, symInc p j = [c1] := by
  match c, h with
  | [c1], h =>
    simp only [isB7, List.contains_iff_mem, singles, List.mem_filterMap, List.mem_range] at h
    obtain ⟨j, hj, hc⟩ := h
    refine ⟨c1, rfl, j, hj, ?_⟩
    split at hc
    · rename_i c' hc'; cases hc; exact hc'
    · cases hc

section Item7

variable {p : Program} {r : ℕ} {zero one B : Ex} {S : List Ex} {vw : List (ℕ × Ex × Ex)}

/-- The presence facts used by item 7: the sums `V_i + W_i` of item 5 and the products `B·x` of
item 6. -/
def Pre7 (p : Program) (r : ℕ) (zero B : Ex) (S : List Ex) (vw : List (ℕ × Ex × Ex))
    (l : List NatNode) : Prop :=
  (∀ e ∈ vw, NatNode.add e.2.1.node e.2.2.node ∈ l) ∧
    ∀ j ∈ List.range r, ∀ x, Packed.incHandles p zero S j = [x] → NatNode.mul B.node x.node ∈ l

theorem Mono.pre7 : Mono (Pre7 p r zero B S vw) :=
  Mono.and (Mono.forall_mem _ fun _ => Mono.mem _)
    (Mono.forall_mem _ fun _ => Mono.forall' fun _ => Mono.imp _ (Mono.mem _))

theorem stateEq_step (hvw : vw.map Prod.fst = decPos 0 p) (i : ℕ) (seen : Bool) (hP : Mono P)
    (hpre : ∀ l, P l → Pre7 p r zero B S vw l ∧ (seen = true → ZPre B.node zero.node l)) :
    Up P (Packed.stateEq B (S.getD i zero) (if i = 0 then one else zero)
        (Packed.inHandles p zero S vw i))
      (step7A (decPos 0 p) i (symIn p i) seen) (step7M (singles p r) i (symIn p i) seen)
      (fun φ l => Cost 1 1 φ ∧ (isC7 i (symIn p i) = true → ZPost B.node zero.node φ l)) := by
  rw [in_corr (S := S) hvw]
  unfold step7A step7M
  by_cases hC : isC7 i (symIn p i) = true
  · have hC2 := hC
    simp [isC7] at hC2
    obtain ⟨hc, hi⟩ := hC2
    rw [hc] at hC ⊢
    simp only [hC, ite_true, List.map_nil, hi, ite_false]
    cases seen
    · exact ((stateEq_up hP B (S.getD i zero) zero []).cost_of rfl rfl).post
        fun φ l h => ⟨h.1, fun _ => h.2 rfl⟩
    · exact (stateEq_up_c hP B (S.getD i zero) zero fun l hl => (hpre l hl).2 rfl).post
        fun φ l h => ⟨h.1, fun _ => h.2⟩
  · have hC' : isC7 i (symIn p i) = false := by simpa using hC
    simp only [hC', Bool.false_eq_true, ite_false]
    refine Up.post (Q := fun φ _ => Cost 1 1 φ) ?_ fun φ l h => ⟨h, fun h' => by simp at h'⟩
    by_cases hA : isA7 (decPos 0 p) (symIn p i) = true
    · obtain ⟨i', rest, hc, hi'⟩ := isA7_sound hA
      rw [hc] at hA ⊢
      simp only [hA, ite_true, List.map_cons, codeEx_v, codeEx_w]
      have hB : isB7 (singles p r) ((3 * i' + 4) :: (3 * i' + 5) :: rest) = false := rfl
      simp only [hB, Bool.false_eq_true, ite_false, List.length_cons]
      obtain ⟨e, he, hl⟩ := realLookup_mem (zero := zero) (by rwa [hvw])
      refine (stateEq_up_a hP B _ _ _ _ _ fun l h => ?_).cost_of (by simp) rfl
      rw [hl]
      exact (hpre l h).1.1 e he
    · have hA' : isA7 (decPos 0 p) (symIn p i) = false := by simpa using hA
      simp only [hA', Bool.false_eq_true, ite_false, Nat.sub_zero]
      by_cases hB : isB7 (singles p r) (symIn p i) = true
      · obtain ⟨c1, hc, j, hj, hcj⟩ := isB7_sound hB
        rw [hc] at hB ⊢
        simp only [hB, ite_true, List.map_cons, List.map_nil, List.length_cons, List.length_nil]
        refine (stateEq_up_b hP B _ _ _ fun l h => ?_).cost_of rfl rfl
        refine (hpre l h).1.2 j (List.mem_range.2 hj) _ ?_
        rw [inc_corr (vw := vw), hcj]
        rfl
      · have hB' : isB7 (singles p r) (symIn p i) = false := by simpa using hB
        simp only [hB', Bool.false_eq_true, ite_false]
        exact ((stateEq_up hP B _ _ _).cost_of (by simp) rfl).post fun φ l h => h.1

/-- The right sides of the states without predecessors: all are the node `0 + B·0`. -/
def Post7 (B z0 : ℕ) (n : ℕ) (φs : List NForm) (l : List NatNode) : Prop :=
  n = 0 ∨ ∃ v z u, l.idxOf? (.const 0) = some z ∧ l.idxOf? (.mul B z) = some u ∧
    l.idxOf? (.add z0 u) = some v ∧ n ≤ φs.countP fun φ => rhsNode φ = some v

theorem Mono.post7 (B z0 n : ℕ) (φs : List NForm) : Mono (Post7 B z0 n φs) :=
  ⟨fun l l' h hl => hl.imp_right fun ⟨v, z, u, h1, h2, h3, h4⟩ =>
    ⟨v, z, u, (Mono.idxOf? _ _).mono l l' h h1, (Mono.idxOf? _ _).mono l l' h h2,
      (Mono.idxOf? _ _).mono l l' h h3, h4⟩⟩

theorem items7_go (hvw : vw.map Prod.fst = decPos 0 p) (L : List ℕ) :
    ∀ (seen : Bool) {P : List NatNode → Prop}, Mono P →
    (∀ l, P l → Pre7 p r zero B S vw l ∧ (seen = true → ZPre B.node zero.node l)) →
    Up P (seqM (L.map fun i => Packed.stateEq B (S.getD i zero) (if i = 0 then one else zero)
        (Packed.inHandles p zero S vw i)))
      (cost7A (symIn p) (decPos 0 p) L seen) (cost7M (symIn p) (singles p r) L seen)
      (fun φs l => CostL L.length L.length L.length φs ∧
        Post7 B.node zero.node (nC7 (symIn p) L) φs l) := by
  induction L with
  | nil => exact fun _ _ _ _ => Up.pure fun _ _ => ⟨⟨rfl, rfl, rfl⟩, .inl rfl⟩
  | cons i L ih =>
    intro seen P hP hpre
    simp only [List.map_cons, seqM, cost7A, cost7M, nC7]
    refine (Up.bind hP (stateEq_step (one := one) hvw i seen hP hpre) fun φ =>
      Up.bind (Mono.and hP (Mono.and (Mono.const _) (Mono.imp _ (Mono.zPost _ _ _))))
        (ih (seen || isC7 i (symIn p i))
          (Mono.and hP (Mono.and (Mono.const _) (Mono.imp _ (Mono.zPost _ _ _))))
          fun l hl => ⟨(hpre l hl.1).1, fun hs => ?_⟩) fun φs =>
        Up.pure fun l hl => ?_).cost_of (by simp) (by simp)
    · cases hs' : seen
      · rw [hs', Bool.false_or] at hs
        exact (hl.2.2 hs).zPre
      · exact (hpre l hl.1).2 hs'
    · obtain ⟨⟨-, ⟨h1, h2⟩, h3⟩, ⟨h4, h5, h6⟩, h7⟩ := hl
      refine ⟨⟨by simp only [encAL, h1, h4, List.length_cons]; omega,
        by simp only [encML, h2, h5, List.length_cons]; omega, by simp [h6]⟩, ?_⟩
      by_cases hC : isC7 i (symIn p i) = true
      · obtain ⟨z, u, v, hz, hu, hv, hφ⟩ := h3 hC
        simp only [hC, ite_true]
        right
        rcases h7 with h0 | ⟨v', z', u', hz', hu', hv', hcount⟩
        · refine ⟨v, z, u, hz, hu, hv, ?_⟩
          rw [h0]
          simp [hφ]
        · rw [hz, Option.some.injEq] at hz'
          subst hz'
          rw [hu, Option.some.injEq] at hu'
          subst hu'
          rw [hv, Option.some.injEq] at hv'
          subst hv'
          refine ⟨v, z, u, hz, hu, hv, ?_⟩
          simp only [List.countP_cons, hφ, decide_true, ite_true]
          omega
      · simp only [hC, Bool.false_eq_true, ite_false, Nat.zero_add]
        rcases h7 with h0 | ⟨v, z, u, hz, hu, hv, hcount⟩
        · exact .inl h0
        · refine .inr ⟨v, z, u, hz, hu, hv, hcount.trans ?_⟩
          rw [List.countP_cons]
          omega

/-- **The bound of item 7.** -/
theorem items7_up (hvw : vw.map Prod.fst = decPos 0 p) (hP : Mono P)
    (hpre : ∀ l, P l → Pre7 p r zero B S vw l) :
    Up P (Packed.items7 p zero one B S vw) (cost7A (symIn p) (decPos 0 p) (List.range p.length) false)
      (cost7M (symIn p) (singles p r) (List.range p.length) false)
      (fun φs l => CostL p.length p.length p.length φs ∧
        Post7 B.node zero.node (nC7 (symIn p) (List.range p.length)) φs l) := by
  have h := items7_go (r := r) (one := one) hvw (List.range p.length) false hP
    fun l hl => ⟨hpre l hl, fun h => absurd h Bool.false_ne_true⟩
  simp only [List.length_range] at h
  exact h

end Item7

end ZInQ.Compiler.NodeBound
