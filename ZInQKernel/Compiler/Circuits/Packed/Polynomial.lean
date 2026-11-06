import ZInQKernel.Compiler.Circuits.Packed.Semantics
import ZInQKernel.Compiler.Circuits.Packed.Valid
import ZInQKernel.Compiler.Circuits.Packed.Sound
import ZInQKernel.Compiler.Circuits.Packed.Complete

/-!
# The compiled circuit of a register machine

For a primitive program `p` valid for `r` registers and `1 ≤ k ≤ r`, the compiled circuit
`𝒞_{p,k}` of the packed-history construction has a natural zero with inputs `a` exactly when
`p` accepts `a` (`compiled_natRel_iff`).

(Blueprint: `compiler/natural/packed/register-machine-polynomial.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Packed

open Natural RM Syntax MvPolynomial Finset

/-- The natural relation of a circuit through assignments agreeing with the inputs. -/
theorem natRel_iff_agree (C : NatCircuit) (T : ExPoly) (hk : C.inputCount ≤ C.varCount)
    (a : Fin C.inputCount → ℕ) :
    C.NatRel T a ↔ ∃ y, Agree (NatCircuit.natPoint C.inputCount (C.varCount - C.inputCount) a
      fun _ => 0) y C.inputCount C.varCount ∧ zv y (C.poly T) = 0 := by
  unfold NatCircuit.NatRel
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨_, fun i hi => ?_, hw⟩
    simp only [NatCircuit.natPoint]
    split_ifs with h1 h2 h3 <;> first | rfl | omega
  · rintro ⟨y, hy, h⟩
    refine ⟨fun j => y (C.inputCount + j), ?_⟩
    have hpt : NatCircuit.natPoint C.inputCount (C.varCount - C.inputCount) a
        (fun j => y (C.inputCount + j)) = y := by
      funext i
      simp only [NatCircuit.natPoint]
      split_ifs with h1 h2
      · rw [hy i (by omega)]; simp [NatCircuit.natPoint, h1]
      · congr 1; omega
      · rw [hy i (by omega)]; simp [NatCircuit.natPoint, h1, h2]
    show zv _ _ = 0
    rw [hpt]; exact h

/-- The run of the packed-history construction from the initial state. -/
theorem construction_run (p : Program) (r k : ℕ) : construction p r k (State.init k) =
    let r0 := constant 0 (State.init k)
    let r1 := constant 1 r0.2
    let rq := fresh r1.2
    let rc := fresh rq.2
    let rK := fresh rc.2
    let rB := fresh rK.2
    let rT := fresh rB.2
    let rF := fresh rT.2
    let rD := fresh rF.2
    let rR := freshN r rD.2
    let rN := freshN r rR.2
    let rS := freshN p.length rN.2
    let res := packedFormulas p r (inputs k) r0.1 r1.1 rq.1 rc.1 rK.1 rB.1 rT.1 rF.1 rD.1 rR.1 rN.1
      rS.1 rS.2
    (NForm.and res.1, res.2) := rfl

theorem getD_of_map_eq {L : List Ex} {n : ℕ} {f : ℕ → Poly}
    (h : L.map Ex.poly = (List.range n).map f) {i : ℕ} (hi : i < n) (d : Ex) :
    (L.getD i d).poly = f i := by
  have hl : L.length = n := by simpa using congrArg List.length h
  have := congrArg (fun l => l.getD i 0) h
  rw [List.getD_eq_getElem _ _ (by simpa [hl] using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa [hl] using hi),
    List.getD_eq_getElem _ _ (by simpa using hi)] at this
  simpa using this

theorem mem_of_map_eq {L : List Ex} {n : ℕ} {f : ℕ → ℕ}
    (h : L.map Ex.poly = (List.range n).map fun i => X (f i)) :
    ∀ e ∈ L, ∃ i < n, e.poly = X (f i) := by
  intro e he
  have : e.poly ∈ (List.range n).map fun i => X (f i) := h ▸ List.mem_map_of_mem he
  obtain ⟨i, hi, h'⟩ := List.mem_map.1 this
  exact ⟨i, List.mem_range.1 hi, h'.symm⟩

/-- The specification of the packed formulas at the initial state, abstract form. -/
theorem packed_spec (p : Program) (r k : ℕ) (zero one q c K B T F D : Ex) (R N S : List Ex)
    (s1 : State) (hz : zero.poly = C 0) (ho : one.poly = C 1) (hq : q.poly = X k)
    (hc : c.poly = X (k + 1)) (hK : K.poly = X (k + 2)) (hB : B.poly = X (k + 3))
    (hT : T.poly = X (k + 4)) (hF : F.poly = X (k + 5)) (hD : D.poly = X (k + 6))
    (hR : R.map Ex.poly = (List.range r).map fun j => X (k + 7 + j))
    (hN : N.map Ex.poly = (List.range r).map fun j => X (k + 7 + r + j))
    (hS : S.map Ex.poly = (List.range p.length).map fun i => X (k + 7 + 2 * r + i))
    (hs1 : s1.next = k + 7 + 2 * r + p.length) :
    Spec (.and ((packedFormulas p r (inputs k) zero one q c K B T F D R N S s1).1.map
        (NForm.toFormula powerTemplate))) {i | i < k} k
      (packedFormulas p r (inputs k) zero one q c K B T F D R N S s1).2.next fun x =>
      ∃ z, AgreeOut x z (· ∈ {i | k ≤ i ∧ i < k + (7 + 2 * r + p.length)} ∪
          vwSet (packedVW p r (inputs k) zero one q c K B T F D R N S s1)) ∧
        True ∧
        ((0 < z (k + 1) ∧ z (k + 2) = 2 ^ z (k + 1) ∧ z (k + 3) = 4 * z (k + 2) ∧
            p.length < z (k + 3) ∧ z (k + 4) = z (k + 3) ^ z k) ∧
          ∀ e ∈ inputs k, nv z e.poly < z (k + 2)) ∧
        (((z (k + 3) : ℤ) * z (k + 5) + 1 = z (k + 5) + z (k + 3) * z (k + 4)) ∧
          ((z (k + 6) : ℤ) + z (k + 5) = z (k + 2) * z (k + 5)) ∧
          (S.map fun e => zv z e.poly).sum = z (k + 5) ∧
          zv z (S.getLastD zero).poly = z (k + 4)) ∧
        (∀ e ∈ S, Nat.land (nv z e.poly) (z (k + 5)) = nv z e.poly) ∧
        (∀ j < r, Nat.land (z (k + 7 + j)) (z (k + 6)) = z (k + 7 + j) ∧
          z (k + 7 + j) < z (k + 4) ∧
          z (k + 2) * z (k + 7 + r + j) = Nat.land (z (k + 7 + j) + z (k + 6))
            (z (k + 2) * z (k + 5))) ∧
        subRel p zero S N (packedVW p r (inputs k) zero one q c K B T F D R N S s1) z ∧
        (∀ j ∈ List.range r,
          zv z (R.getD j zero).poly + zv z B.poly *
              ((decHandles p zero (packedVW p r (inputs k) zero one q c K B T F D R N S s1) j).map
                fun e => zv z e.poly).sum =
            zv z ((inputs k).getD j zero).poly + zv z B.poly * zv z (R.getD j zero).poly +
              zv z B.poly * ((incHandles p zero S j).map fun e => zv z e.poly).sum) ∧
        (∀ i ∈ List.range p.length,
          zv z (S.getD i zero).poly = zv z (if i = 0 then one else zero).poly +
            zv z B.poly * ((inHandles p zero S
              (packedVW p r (inputs k) zero one q c K B T F D R N S s1) i).map
                fun e => zv z e.poly).sum) := by
  set U : Set ℕ := {i | i < k} ∪ {i | k ≤ i ∧ i < k + (7 + 2 * r + p.length)}
  have hU : ∀ i ∈ U, i < s1.next := by
    intro i hi; rcases hi with hi | hi
    · simp only [Set.mem_setOf_eq] at hi; omega
    · simp only [Set.mem_setOf_eq] at hi; omega
  have hmem : ∀ i, i < k + 7 + 2 * r + p.length → i ∈ U := by
    intro i hi
    by_cases h : i < k
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by omega⟩
  have hP := packedFormulas_specE (τ := powerTemplate) powerSpec_hierarchical_powerTemplate p r
    (inputs k) zero one q c K B T F D R N S s1 (U := U) (pR := k + 7) (pN := k + 7 + r)
    hz ho hq hc hK hB hT hF hD
    (fun j hj => getD_of_map_eq hR hj zero) (fun j hj => getD_of_map_eq hN hj zero)
    (fun e he => by
      obtain ⟨j, hj, h⟩ := mem_of_map_eq hR e he; exact ⟨_, hmem _ (by omega), h⟩)
    (fun e he => by
      obtain ⟨j, hj, h⟩ := mem_of_map_eq hN e he; exact ⟨_, hmem _ (by omega), h⟩)
    (fun e he => by
      obtain ⟨j, hj, h⟩ := mem_of_map_eq hS e he; exact ⟨_, hmem _ (by omega), h⟩)
    (fun e he => by
      simp only [inputs, List.mem_map, List.mem_range] at he
      obtain ⟨i, hi, rfl⟩ := he; exact ⟨i, Or.inl hi, rfl⟩)
    ⟨hmem _ (by omega), hmem _ (by omega), hmem _ (by omega), hmem _ (by omega),
      hmem _ (by omega), hmem _ (by omega), hmem _ (by omega)⟩
    (fun j hj => hmem _ (by omega)) (fun j hj => hmem _ (by omega)) hU
  have hE := SpecE.expose {i | i < k} k (7 + 2 * r + p.length)
  rw [show k + (7 + 2 * r + p.length) = s1.next by omega] at hE
  have := (hE.append (hP.mono fun i hi => by
    rcases hi with hi | hi <;> simp only [Set.mem_union, Set.mem_setOf_eq] at hi ⊢ <;> omega)
    (fun i hi => hi)).close
  have hS' : k + (7 + 2 * r + p.length) = s1.next := by omega
  simp only [List.nil_append] at this
  rw [hS']
  convert this using 3

/-! ### Lists and sums -/

theorem sum_map_filter_range (f : ℕ → ℤ) (P : ℕ → Prop) [DecidablePred P] (m : ℕ) :
    (((List.range m).filter fun i => decide (P i)).map f).sum =
      ∑ i ∈ Finset.range m, if P i then f i else 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    by_cases h : P m <;> simp [h]

theorem sum_map_inHandles (p : Program) (zero : Ex) (S : List Ex) (vw : List (ℕ × Ex × Ex))
    (i : ℕ) (g : Ex → ℤ) :
    ((inHandles p zero S vw i).map g).sum = ∑ i' ∈ Finset.range p.length,
      ((if incTo p i' i then g (S.getD i' zero) else 0) +
        (if nzTo p i' i then g (lookupVW zero vw i').1 else 0) +
        (if zTo p i' i then g (lookupVW zero vw i').2 else 0)) := by
  unfold inHandles
  generalize p.length = m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]
    congr 1
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_append,
      List.sum_append]
    split_ifs <;> simp

theorem sum_map_range_X (f : ℕ → ℕ) (x : ℕ → ℕ) (L : List Ex) (n : ℕ)
    (h : L.map Ex.poly = (List.range n).map fun i => X (f i)) :
    (L.map fun e => zv x e.poly) = (List.range n).map fun i => (x (f i) : ℤ) := by
  have : (L.map fun e => zv x e.poly) = (L.map Ex.poly).map (zv x) := by simp [List.map_map]
  rw [this, h, List.map_map]
  exact List.map_congr_left fun i _ => by simp

theorem list_sum_range (f : ℕ → ℤ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The sub instruction indices are those of the program. -/
theorem mem_decIdx : ∀ (rest : List Instr) (i₀ i : ℕ),
    i ∈ decIdx rest i₀ ↔ i₀ ≤ i ∧ ∃ j x y, rest[i - i₀]? = some (.dec j x y)
  | [], i₀, i => by simp [decIdx]
  | .dec j x y :: rest, i₀, i => by
    simp only [decIdx, List.mem_cons, mem_decIdx rest (i₀ + 1) i]
    constructor
    · rintro (rfl | ⟨h1, j', x', y', h2⟩)
      · exact ⟨le_rfl, j, x, y, by simp⟩
      · refine ⟨by omega, j', x', y', ?_⟩
        rw [show i - i₀ = (i - (i₀ + 1)) + 1 by omega]; simpa using h2
    · rintro ⟨h1, j', x', y', h2⟩
      rcases Nat.lt_or_ge i₀ i with h | h
      · right
        refine ⟨by omega, j', x', y', ?_⟩
        rw [show i - i₀ = (i - (i₀ + 1)) + 1 by omega] at h2; simpa using h2
      · left; omega
  | .inc j x :: rest, i₀, i => by
    simp only [decIdx, mem_decIdx rest (i₀ + 1) i]
    constructor
    · rintro ⟨h1, j', x', y', h2⟩
      refine ⟨by omega, j', x', y', ?_⟩
      rw [show i - i₀ = (i - (i₀ + 1)) + 1 by omega]; simpa using h2
    · rintro ⟨h1, j', x', y', h2⟩
      rcases Nat.lt_or_ge i₀ i with h | h
      · refine ⟨by omega, j', x', y', ?_⟩
        rw [show i - i₀ = (i - (i₀ + 1)) + 1 by omega] at h2; simpa using h2
      · rw [show i - i₀ = 0 by omega] at h2; simp at h2
  | .halt :: rest, i₀, i => by
    simp only [decIdx, mem_decIdx rest (i₀ + 1) i]
    constructor
    · rintro ⟨h1, j', x', y', h2⟩
      refine ⟨by omega, j', x', y', ?_⟩
      rw [show i - i₀ = (i - (i₀ + 1)) + 1 by omega]; simpa using h2
    · rintro ⟨h1, j', x', y', h2⟩
      rcases Nat.lt_or_ge i₀ i with h | h
      · refine ⟨by omega, j', x', y', ?_⟩
        rw [show i - i₀ = (i - (i₀ + 1)) + 1 by omega] at h2; simpa using h2
      · rw [show i - i₀ = 0 by omega] at h2; simp at h2

/-- For a sub instruction `i`, the lookup of its branch histories finds its entry. -/
theorem lookupVW_of_decOn {p : Program} {zero : Ex} {vw : List (ℕ × Ex × Ex)}
    (hvw : vw.map (·.1) = decIdx p 0) {i j : ℕ} (hi : decOn p j i) :
    ∃ e ∈ vw, e.1 = i ∧ lookupVW zero vw i = e.2 := by
  obtain ⟨x, y, hxy⟩ := hi
  have hmem : i ∈ vw.map (·.1) := by
    rw [hvw, mem_decIdx]; exact ⟨Nat.zero_le _, j, x, y, by simpa using hxy⟩
  obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 hmem
  cases h : vw.find? (fun e => e.1 == e₀.1) with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd (h e₀ he₀) (by simp)
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have he1 := List.find?_some h
    simp only [beq_iff_eq] at he1
    exact ⟨e, he, he1, by simp [lookupVW, h]⟩

theorem getLastD_eq_getD {L : List Ex} (d : Ex) : L.getLastD d = L.getD (L.length - 1) d := by
  cases L using List.reverseRecOn with
  | nil => rfl
  | append_singleton l e =>
    simp [List.getLastD_eq_getLast?, List.getD_eq_getElem?_getD]

theorem getD_mem {L : List Ex} {i : ℕ} (hi : i < L.length) (d : Ex) : L.getD i d ∈ L := by
  rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi

theorem lookupVW_isNat {zero : Ex} (hz : zero.poly = C 0) {vw : List (ℕ × Ex × Ex)}
    (hvw : ∀ e ∈ vw, ∃ c, e.2.1.poly = X c ∧ e.2.2.poly = X (c + 1)) (i : ℕ) :
    IsNat (lookupVW zero vw i).1.poly ∧ IsNat (lookupVW zero vw i).2.poly := by
  unfold lookupVW
  cases h : vw.find? (fun e => e.1 == i) with
  | none =>
    simp only [Option.map_none, Option.getD_none, hz]
    exact ⟨IsNat.C_of_nonneg le_rfl, IsNat.C_of_nonneg le_rfl⟩
  | some v =>
    obtain ⟨c, h1, h2⟩ := hvw v (List.mem_of_find?_eq_some h)
    simp [h1, h2, IsNat.X]

/-- The relation of the packed formulas, read at an assignment `z`. -/
def PackedRel (p : Program) (r k : ℕ) (zero one B : Ex) (R N S : List Ex)
    (vw : List (ℕ × Ex × Ex)) (z : ℕ → ℕ) : Prop :=
  ((0 < z (k + 1) ∧ z (k + 2) = 2 ^ z (k + 1) ∧ z (k + 3) = 4 * z (k + 2) ∧
      p.length < z (k + 3) ∧ z (k + 4) = z (k + 3) ^ z k) ∧
    ∀ e ∈ inputs k, nv z e.poly < z (k + 2)) ∧
  (((z (k + 3) : ℤ) * z (k + 5) + 1 = z (k + 5) + z (k + 3) * z (k + 4)) ∧
    ((z (k + 6) : ℤ) + z (k + 5) = z (k + 2) * z (k + 5)) ∧
    (S.map fun e => zv z e.poly).sum = z (k + 5) ∧
    zv z (S.getLastD zero).poly = z (k + 4)) ∧
  (∀ e ∈ S, Nat.land (nv z e.poly) (z (k + 5)) = nv z e.poly) ∧
  (∀ j < r, Nat.land (z (k + 7 + j)) (z (k + 6)) = z (k + 7 + j) ∧
    z (k + 7 + j) < z (k + 4) ∧
    z (k + 2) * z (k + 7 + r + j) = Nat.land (z (k + 7 + j) + z (k + 6))
      (z (k + 2) * z (k + 5))) ∧
  subRel p zero S N vw z ∧
  (∀ j ∈ List.range r,
    zv z (R.getD j zero).poly + zv z B.poly *
        ((decHandles p zero vw j).map fun e => zv z e.poly).sum =
      zv z ((inputs k).getD j zero).poly + zv z B.poly * zv z (R.getD j zero).poly +
        zv z B.poly * ((incHandles p zero S j).map fun e => zv z e.poly).sum) ∧
  (∀ i ∈ List.range p.length,
    zv z (S.getD i zero).poly = zv z (if i = 0 then one else zero).poly +
      zv z B.poly * ((inHandles p zero S vw i).map fun e => zv z e.poly).sum)

/-- **From the relation to the packed conditions.** -/
theorem packedRel_conditions {p : Program} {r k : ℕ} (hp : p.Valid r) {a : Fin k → ℕ}
    {zero one B : Ex} {R N S : List Ex} {vw : List (ℕ × Ex × Ex)} (hz : zero.poly = C 0)
    (ho : one.poly = C 1) (hB : B.poly = X (k + 3))
    (hR : R.map Ex.poly = (List.range r).map fun j => X (k + 7 + j))
    (hN : N.map Ex.poly = (List.range r).map fun j => X (k + 7 + r + j))
    (hS : S.map Ex.poly = (List.range p.length).map fun i => X (k + 7 + 2 * r + i))
    (hvw : vw.map (·.1) = decIdx p 0)
    (hvw' : ∀ e ∈ vw, ∃ c, e.2.1.poly = X c ∧ e.2.2.poly = X (c + 1))
    {z : ℕ → ℕ} (hza : ∀ i : Fin k, z i = a i) (h : PackedRel p r k zero one B R N S vw z) :
    PackedConditions p r k a (z k) (z (k + 1)) (z (k + 2)) (z (k + 3)) (z (k + 4)) (z (k + 5))
      (z (k + 6)) (fun j => z (k + 7 + j)) (fun j => z (k + 7 + r + j))
      (fun i => z (k + 7 + 2 * r + i)) (fun i => nv z (lookupVW zero vw i).1.poly)
      (fun i => nv z (lookupVW zero vw i).2.poly) := by
  obtain ⟨⟨⟨h1, h2, h3, h4, h5⟩, h6⟩, ⟨h7, h8, h9, h10⟩, h11, h12, h13, h14, h15⟩ := h
  have hSlen : S.length = p.length := by simpa using congrArg List.length hS
  have hSget : ∀ i < p.length, (S.getD i zero).poly = X (k + 7 + 2 * r + i) :=
    fun i hi => getD_of_map_eq hS hi zero
  have hlook := lookupVW_isNat hz hvw'
  have hm0 := hp.pos
  refine ⟨h1, h2, h3, h4, h5, fun i => ?_, by exact_mod_cast h7, by exact_mod_cast h8, ?_, ?_,
    fun i hi => ?_, fun j hj => (h12 j hj).1, fun j hj => (h12 j hj).2.1,
    fun j hj => (h12 j hj).2.2, fun i hi j hj => ?_, fun j hj => ?_, fun i hi => ?_⟩
  · have := h6 ⟨i, X i⟩ (by simp [inputs, i.isLt])
    rw [nv_X, hza] at this; exact this
  · rw [sum_map_range_X _ z S _ hS, list_sum_range] at h9
    exact_mod_cast h9
  · rw [getLastD_eq_getD, hSlen, hSget _ (by omega), zv_X] at h10
    exact_mod_cast h10
  · have := h11 (S.getD i zero) (getD_mem (by omega) zero)
    rwa [hSget i hi, nv_X] at this
  · obtain ⟨e, he, he1, hle⟩ := lookupVW_of_decOn hvw hj
    have hjr := decOn_lt hp hi hj
    obtain ⟨hA, hE⟩ := h13 e he
    rw [he1, decReg_of_decOn hj, getD_of_map_eq hN hjr zero, hSget i hi, nv_X, nv_X] at hA
    rw [he1, hSget i hi, zv_X] at hE
    obtain ⟨c, hc1, hc2⟩ := hvw' e he
    show nv z (lookupVW zero vw i).1.poly = _ ∧ _
    rw [hle, hc1, hc2, nv_X, nv_X]
    rw [hc1, nv_X] at hA
    rw [hc1, hc2, zv_X, zv_X] at hE
    exact ⟨hA, by exact_mod_cast hE⟩
  · have := h14 j (List.mem_range.2 hj)
    rw [getD_of_map_eq hR hj zero, hB, zv_X, zv_X] at this
    have hdec : ((decHandles p zero vw j).map fun e => zv z e.poly).sum =
        ((decSum p (fun i => nv z (lookupVW zero vw i).1.poly) j : ℕ) : ℤ) := by
      unfold decHandles decSum
      rw [List.map_map, sum_map_filter_range]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs
      · exact (hlook i).1.zv_eq z
      · rfl
    have hinc : ((incHandles p zero S j).map fun e => zv z e.poly).sum =
        ((incSum p (fun i => z (k + 7 + 2 * r + i)) j : ℕ) : ℤ) := by
      unfold incHandles incSum
      rw [List.map_map, sum_map_filter_range]
      push_cast
      refine Finset.sum_congr rfl fun i hi => ?_
      split_ifs
      · show zv z (S.getD i zero).poly = _
        rw [hSget i (Finset.mem_range.1 hi), zv_X]
      · rfl
    have hι : zv z ((inputs k).getD j zero).poly = (initFile a j : ℤ) := by
      by_cases hjk : j < k
      · rw [getD_of_map_eq (n := k) (f := fun i => X i) (by simp [inputs, List.map_map]) hjk,
          zv_X, initFile_of_lt a hjk, hza ⟨j, hjk⟩]
      · rw [List.getD_eq_default _ _ (by simpa [inputs] using hjk), hz, zv_C,
          initFile_of_le a (by omega)]; simp
    rw [hdec, hinc, hι] at this
    exact_mod_cast this
  · have := h15 i (List.mem_range.2 hi)
    rw [hSget i hi, hB, zv_X, zv_X, sum_map_inHandles] at this
    have hin : (∑ i' ∈ Finset.range p.length,
        ((if incTo p i' i then zv z (S.getD i' zero).poly else 0) +
          (if nzTo p i' i then zv z (lookupVW zero vw i').1.poly else 0) +
          (if zTo p i' i then zv z (lookupVW zero vw i').2.poly else 0))) =
        ((inSum p (fun i => z (k + 7 + 2 * r + i)) (fun i => nv z (lookupVW zero vw i).1.poly)
          (fun i => nv z (lookupVW zero vw i).2.poly) i : ℕ) : ℤ) := by
      unfold inSum
      push_cast
      refine Finset.sum_congr rfl fun i' hi' => ?_
      rw [hSget i' (Finset.mem_range.1 hi'), zv_X, (hlook i').1.zv_eq, (hlook i').2.zv_eq]
    rw [hin] at this
    have he : zv z (if i = 0 then one else zero).poly = ((if i = 0 then 1 else 0 : ℕ) : ℤ) := by
      split_ifs <;> simp [ho, hz]
    rw [he] at this
    exact_mod_cast this

end ZInQ.Compiler.Packed
