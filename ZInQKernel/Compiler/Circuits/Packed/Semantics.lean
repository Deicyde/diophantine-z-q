import ZInQKernel.Compiler.Circuits.Packed.Construction
import ZInQKernel.Compiler.Circuits.Packed.Counts
import ZInQKernel.Compiler.Circuits.Exposed
import ZInQKernel.Compiler.Circuits.PowerTemplate

/-!
# The packed-history construction with its macros read as relations

The phases of the packed-history construction, run on fresh variables at known positions,
satisfy specifications whose relations are the items of the packed conditions; the sub-branch
phase exposes the branch histories `V_i, W_i`. (Helpers for
`compiler/natural/packed/register-machine-polynomial.md`.)
-/

noncomputable section

namespace ZInQ.Compiler.Packed

open Natural RM Syntax MvPolynomial

variable {τ : ExPoly}

/-! ### Fresh variable lists -/

theorem freshN_spec (n : ℕ) (s : State) :
    ((freshN n s).1.map Ex.poly = (List.range n).map fun i => X (s.next + i)) ∧
      (freshN n s).2.next = s.next + n := by
  induction n generalizing s with
  | zero => simp [freshN]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (fresh s).2
    simp only [freshN, NM.bind_apply, NM.pure_apply, List.map_cons, fresh_apply_poly]
    rw [h1, h2, fresh_apply_next, List.range_succ_eq_map]
    refine ⟨?_, by ring⟩
    simp only [List.map_cons, List.map_map, add_zero, List.cons.injEq, true_and]
    exact List.map_congr_left fun i _ => by simp [Function.comp, Nat.add_assoc, Nat.add_comm 1 i]

theorem freshN_getD_poly {n : ℕ} {s : State} {i : ℕ} (hi : i < n) (d : Ex) :
    ((freshN n s).1.getD i d).poly = X (s.next + i) := by
  induction n generalizing s i with
  | zero => omega
  | succ n ih =>
    simp only [freshN, NM.bind_apply, NM.pure_apply]
    rcases i with _ | i
    · simp [fresh_apply_poly]
    · simp only [List.getD_cons_succ]
      rw [ih (by omega), fresh_apply_next]; ring_nf

/-! ### Formula-list constructions -/

/-- A formula-list construction satisfies `SpecL` with relation `R` at every state above `U`. -/
def MSpecL (τ : ExPoly) (m : NM (List NForm)) (U : Set ℕ) (R : (ℕ → ℕ) → Prop) : Prop :=
  ∀ s : State, (∀ i ∈ U, i < s.next) →
    SpecL ((m s).1.map (NForm.toFormula τ)) U s.next (m s).2.next R

theorem MSpecL.congr {m : NM (List NForm)} {U : Set ℕ} {R R' : (ℕ → ℕ) → Prop}
    (h : MSpecL τ m U R) (hR : ∀ x, R x ↔ R' x) : MSpecL τ m U R' := fun s hs =>
  let h' := h s hs; ⟨h'.le, h'.loc, fun x => (h'.sem x).trans (hR x)⟩

theorem MSpecL.appendM {m₁ m₂ : NM (List NForm)} {U : Set ℕ} {R₁ R₂ : (ℕ → ℕ) → Prop}
    (h₁ : MSpecL τ m₁ U R₁) (h₂ : MSpecL τ m₂ U R₂) :
    MSpecL τ (Packed.appendM m₁ m₂) U fun x => R₁ x ∧ R₂ x := fun s hs => by
  have k₁ := h₁ s hs
  have k₂ := h₂ (m₁ s).2 fun i hi => lt_of_lt_of_le (hs i hi) k₁.le
  have := SpecL.append' k₁ k₂ hs
  simpa [Packed.appendM] using this

theorem MSpecL.seqM {ms : List (NM NForm)} {U : Set ℕ} {Rs : List ((ℕ → ℕ) → Prop)}
    (h : List.Forall₂ (fun m R => MSpec τ m U R) ms Rs) :
    MSpecL τ (Natural.seqM ms) U fun x => ∀ R ∈ Rs, R x := fun s hs => seqM_specL ms Rs h s hs

theorem MSpecL.seqM_map {γ : Type} {U : Set ℕ} (l : List γ) (g : γ → NM NForm)
    (Rg : γ → (ℕ → ℕ) → Prop) (h : ∀ x ∈ l, MSpec τ (g x) U (Rg x)) :
    MSpecL τ (Natural.seqM (l.map g)) U fun x => ∀ y ∈ l, Rg y x := fun s hs =>
  seqM_map_specL l g Rg h s hs

theorem MSpecL.pure_nil {U : Set ℕ} : MSpecL τ (Pure.pure []) U fun _ => True := fun s _ => by
  simpa using SpecL.nil (U := U) s.next

theorem MSpecL.seqConcat_map {γ : Type} {U : Set ℕ} (l : List γ) (g : γ → NM (List NForm))
    (Rg : γ → (ℕ → ℕ) → Prop) (h : ∀ x ∈ l, MSpecL τ (g x) U (Rg x)) :
    MSpecL τ (seqConcat (l.map g)) U fun x => ∀ y ∈ l, Rg y x := by
  induction l with
  | nil => exact (MSpecL.pure_nil (τ := τ)).congr fun x => by simp
  | cons y ys ih =>
    have := MSpecL.appendM (h y List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
    exact this.congr fun x => by simp

/-! ### Item 1 -/

theorem items1_spec (hpow : PowerSpec τ .hierarchical) (p : Program) (a : List Ex)
    (zero q c K B T : Ex) {U : Set ℕ} {pq pc pK pB pT : ℕ} (hz : zero.poly = C 0)
    (hq : q.poly = X pq) (hc : c.poly = X pc) (hK : K.poly = X pK) (hB : B.poly = X pB)
    (hT : T.poly = X pT) (hpos : pq ∈ U ∧ pc ∈ U ∧ pK ∈ U ∧ pB ∈ U ∧ pT ∈ U)
    (ha : ∀ e ∈ a, ∃ i ∈ U, e.poly = X i) :
    MSpecL τ (items1 p a zero q c K B T) U fun x =>
        (0 < x pc ∧ x pK = 2 ^ x pc ∧ x pB = 4 * x pK ∧ p.length < x pB ∧ x pT = x pB ^ x pq) ∧
        ∀ e ∈ a, nv x e.poly < x pK := by
  obtain ⟨hq', hc', hK', hB', hT'⟩ := hpos
  have hX : ∀ {i}, i ∈ U → VarsIn (X i : Poly) (· ∈ U) := fun h => VarsIn.X h
  unfold items1
  rw [seqM_append]
  refine (MSpecL.appendM (MSpecL.seqM (Rs := [fun x => 0 < x pc, fun x => x pK = 2 ^ x pc,
    fun x => x pB = 4 * x pK, fun x => p.length < x pB, fun x => x pT = x pB ^ x pq]) ?_)
    (MSpecL.seqM_map a (fun ai => lt ai K) (fun e x => nv x e.poly < x pK) fun e he => ?_)).congr
    fun x => by simp
  · refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))
    · refine (lt_spec (VarsIn.C 0 _) (hX hc') (IsNat.C_of_nonneg le_rfl) (IsNat.X _) hz hc).congr
        fun x => ?_
      simp [nv]
    · refine MSpec.expr_bind (IsExpr.constant 2) fun two htwo => ?_
      refine (hpow U _ _ _ (hX hK') (VarsIn.C 2 _) (hX hc') (IsNat.X _)
        (IsNat.C_of_nonneg (by norm_num)) (IsNat.X _) K two c hK htwo hc).congr fun x => ?_
      simp [nv]
    · refine MSpec.expr_bind (IsExpr.scale 4 K) fun e he => ?_
      refine (MSpec.eq' (U := U) hB (he.trans (by rw [hK])) (hX hB')
        ((VarsIn.C 4 _).mul (hX hK'))).congr fun x => ?_
      simp only [zv_X, zv_mul, zv_C]
      omega
    · refine MSpec.expr_bind (IsExpr.constant p.length) fun e he => ?_
      refine (lt_spec (VarsIn.C _ _) (hX hB') (IsNat.C_of_nonneg (by positivity)) (IsNat.X _) he
        hB).congr fun x => ?_
      simp [nv]
    · refine (hpow U _ _ _ (hX hT') (hX hB') (hX hq') (IsNat.X _) (IsNat.X _) (IsNat.X _) T B q
        hT hB hq).congr fun x => ?_
      simp [nv]
  · obtain ⟨i, hi, he'⟩ := ha e he
    refine (lt_spec (hX hi) (hX hK') (IsNat.X _) (IsNat.X _) he' hK).congr fun x => ?_
    rw [he', nv_X, nv_X]

/-! ### Items 2, 3, 4 -/

theorem varsIn_of_mem {S : List Ex} {U : Set ℕ} (hS : ∀ e ∈ S, ∃ i ∈ U, e.poly = X i) :
    ∀ e ∈ S, VarsIn e.poly (· ∈ U) := fun e he => by
  obtain ⟨i, hi, h⟩ := hS e he; rw [h]; exact VarsIn.X hi

theorem isNat_of_mem {S : List Ex} {U : Set ℕ} (hS : ∀ e ∈ S, ∃ i ∈ U, e.poly = X i) :
    ∀ e ∈ S, IsNat e.poly := fun e he => by
  obtain ⟨i, -, h⟩ := hS e he; rw [h]; exact IsNat.X i

theorem getLastD_mem_or (S : List Ex) (d : Ex) : S.getLastD d ∈ S ∨ S.getLastD d = d := by
  cases S using List.reverseRecOn with
  | nil => right; rfl
  | append_singleton l e => left; simp

theorem items2_spec (zero one K B T F D : Ex) (S : List Ex) {U : Set ℕ} {pK pB pT pF pD : ℕ}
    (hzero : zero.poly = C 0) (hone : one.poly = C 1) (hK : K.poly = X pK) (hB : B.poly = X pB) (hT : T.poly = X pT)
    (hF : F.poly = X pF) (hD : D.poly = X pD) (hpos : pK ∈ U ∧ pB ∈ U ∧ pT ∈ U ∧ pF ∈ U ∧ pD ∈ U)
    (hS : ∀ e ∈ S, ∃ i ∈ U, e.poly = X i) :
    MSpecL τ (items2 zero one K B T F D S) U fun x =>
      ((x pB : ℤ) * x pF + 1 = x pF + x pB * x pT) ∧ ((x pD : ℤ) + x pF = x pK * x pF) ∧
      (S.map fun e => zv x e.poly).sum = x pF ∧ zv x (S.getLastD zero).poly = x pT := by
  obtain ⟨hK', hB', hT', hF', hD'⟩ := hpos
  have hX : ∀ {i}, i ∈ U → VarsIn (X i : Poly) (· ∈ U) := fun h => VarsIn.X h
  unfold items2
  refine (MSpecL.seqM (Rs := [fun x => (x pB : ℤ) * x pF + 1 = x pF + x pB * x pT,
    fun x => (x pD : ℤ) + x pF = x pK * x pF, fun x => (S.map fun e => zv x e.poly).sum = x pF,
    fun x => zv x (S.getLastD zero).poly = x pT]) ?_).congr fun x => by simp
  refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
  · refine MSpec.expr_bind (IsExpr.mulL _) fun e1 he1 => ?_
    refine MSpec.expr_bind (IsExpr.addL _) fun e2 he2 => ?_
    refine MSpec.expr_bind (IsExpr.mulL _) fun e3 he3 => ?_
    refine MSpec.expr_bind (IsExpr.addL _) fun e4 he4 => ?_
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons,
      List.sum_nil, mul_one, add_zero, hB, hF, hT, hone, he1, he3] at he2 he4
    refine (MSpec.eq' (U := U) he2 he4 ((hX hB').mul (hX hF') |>.add (VarsIn.C _ _))
      ((hX hF').add ((hX hB').mul (hX hT')))).congr fun x => ?_
    simp
  · refine MSpec.expr_bind (IsExpr.addL _) fun e1 he1 => ?_
    refine MSpec.expr_bind (IsExpr.mulL _) fun e2 he2 => ?_
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons,
      List.sum_nil, mul_one, add_zero, hK, hF, hD] at he1 he2
    refine (MSpec.eq' (U := U) he1 he2 ((hX hD').add (hX hF')) ((hX hK').mul (hX hF'))).congr
      fun x => ?_
    simp
  · refine MSpec.expr_bind (IsExpr.addL _) fun e1 he1 => ?_
    refine (MSpec.eq' (U := U) he1 hF (VarsIn.list_sum fun f hf => ?_) (hX hF')).congr
      fun x => ?_
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hf
      exact varsIn_of_mem hS e he
    · rw [zv_list_sum, List.map_map, zv_X]; rfl
  · refine (MSpec.eq' (U := U) rfl hT ?_ (hX hT')).congr fun x => by rw [zv_X]
    rcases getLastD_mem_or S zero with h | h
    · exact varsIn_of_mem hS _ h
    · rw [h, hzero]; exact VarsIn.C _ _

theorem items3_spec (hpow : PowerSpec τ .hierarchical) (F : Ex) (S : List Ex) {U : Set ℕ} {pF : ℕ} (hF : F.poly = X pF)
    (hF' : pF ∈ U) (hS : ∀ e ∈ S, ∃ i ∈ U, e.poly = X i) :
    MSpecL τ (items3 F S) U fun x => ∀ e ∈ S, Nat.land (nv x e.poly) (x pF) = nv x e.poly := by
  unfold items3
  refine (MSpecL.seqM_map S _ (fun e x => Nat.land (nv x e.poly) (x pF) = nv x e.poly)
    fun e he => ?_)
  exact (mask_spec hpow (varsIn_of_mem hS e he) (VarsIn.X hF')
    (isNat_of_mem hS e he) (IsNat.X _) rfl hF).congr fun x => by rw [nv_X]

theorem registerMasks_spec (hpow : PowerSpec τ .hierarchical) (K D T F Rj Nj : Ex) {U : Set ℕ}
    {pK pD pT pF pr pn : ℕ} (hK : K.poly = X pK) (hD : D.poly = X pD) (hT : T.poly = X pT)
    (hF : F.poly = X pF) (hr : Rj.poly = X pr) (hn : Nj.poly = X pn)
    (hpos : pK ∈ U ∧ pD ∈ U ∧ pT ∈ U ∧ pF ∈ U ∧ pr ∈ U ∧ pn ∈ U) :
    MSpecL τ (registerMasks K D T F Rj Nj) U fun x =>
      Nat.land (x pr) (x pD) = x pr ∧ x pr < x pT ∧
        x pK * x pn = Nat.land (x pr + x pD) (x pK * x pF) := by
  obtain ⟨hK', hD', hT', hF', hr', hn'⟩ := hpos
  have hX : ∀ {i}, i ∈ U → VarsIn (X i : Poly) (· ∈ U) := fun h => VarsIn.X h
  unfold registerMasks
  refine (MSpecL.seqM (Rs := [fun x => Nat.land (x pr) (x pD) = x pr, fun x => x pr < x pT,
    fun x => x pK * x pn = Nat.land (x pr + x pD) (x pK * x pF)]) ?_).congr fun x => by simp
  refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
  · exact (mask_spec hpow (hX hr') (hX hD') (IsNat.X _) (IsNat.X _) hr hD).congr fun x => by
      simp [nv_X]
  · exact (lt_spec (hX hr') (hX hT') (IsNat.X _) (IsNat.X _) hr hT).congr fun x => by simp [nv_X]
  · refine MSpec.expr_bind (IsExpr.mulL _) fun e1 he1 => ?_
    refine MSpec.expr_bind (IsExpr.addL _) fun e2 he2 => ?_
    refine MSpec.expr_bind (IsExpr.mulL _) fun e3 he3 => ?_
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons,
      List.sum_nil, mul_one, add_zero, hK, hn, hr, hD, hF] at he1 he2 he3
    refine (bitAnd_spec hpow ((hX hK').mul (hX hn')) ((hX hr').add (hX hD'))
      ((hX hK').mul (hX hF')) ((IsNat.X _).mul (IsNat.X _)) ((IsNat.X _).add (IsNat.X _))
      ((IsNat.X _).mul (IsNat.X _)) he1 he2 he3).congr fun x => ?_
    rw [nv_mul (IsNat.X _) (IsNat.X _), nv_add (IsNat.X _) (IsNat.X _),
      nv_mul (IsNat.X _) (IsNat.X _)]
    simp [nv_X]

theorem items4_spec (hpow : PowerSpec τ .hierarchical) (r : ℕ) (zero K D T F : Ex)
    (R N : List Ex) {U : Set ℕ} {pK pD pT pF pR pN : ℕ} (hK : K.poly = X pK) (hD : D.poly = X pD)
    (hT : T.poly = X pT) (hF : F.poly = X pF)
    (hR : ∀ j < r, (R.getD j zero).poly = X (pR + j))
    (hN : ∀ j < r, (N.getD j zero).poly = X (pN + j))
    (hpos : pK ∈ U ∧ pD ∈ U ∧ pT ∈ U ∧ pF ∈ U) (hRU : ∀ j < r, pR + j ∈ U)
    (hNU : ∀ j < r, pN + j ∈ U) :
    MSpecL τ (items4 r zero K D T F R N) U fun x => ∀ j < r,
      Nat.land (x (pR + j)) (x pD) = x (pR + j) ∧ x (pR + j) < x pT ∧
        x pK * x (pN + j) = Nat.land (x (pR + j) + x pD) (x pK * x pF) := by
  unfold items4
  refine (MSpecL.seqConcat_map (List.range r) _ (fun j x =>
    Nat.land (x (pR + j)) (x pD) = x (pR + j) ∧ x (pR + j) < x pT ∧
      x pK * x (pN + j) = Nat.land (x (pR + j) + x pD) (x pK * x pF)) fun j hj => ?_).congr
    fun x => by simp
  have hj' := List.mem_range.1 hj
  exact registerMasks_spec hpow K D T F _ _ hK hD hT hF (hR j hj') (hN j hj')
    ⟨hpos.1, hpos.2.1, hpos.2.2.1, hpos.2.2.2, hRU j hj', hNU j hj'⟩

/-! ### Item 5: the sub branches, with exposed branch histories -/

/-- The positions of the branch histories. -/
def vwSet (vw : List (ℕ × Ex × Ex)) : Set ℕ :=
  {c | ∃ e ∈ vw, e.2.1.poly = X c ∨ e.2.2.poly = X c}

/-- The relations of item 5: `V_i = S_i AND N_j` and `S_i = V_i + W_i`. -/
def subRel (P : Program) (zero : Ex) (S N : List Ex) (vw : List (ℕ × Ex × Ex)) (x : ℕ → ℕ) :
    Prop :=
  ∀ e ∈ vw, nv x e.2.1.poly = Nat.land (nv x (S.getD e.1 zero).poly)
      (nv x (N.getD (decReg P e.1) zero).poly) ∧
    zv x (S.getD e.1 zero).poly = zv x e.2.1.poly + zv x e.2.2.poly

theorem getD_vars {S : List Ex} {U : Set ℕ} (hS : ∀ e ∈ S, ∃ i ∈ U, e.poly = X i) {zero : Ex}
    (hzero : zero.poly = C 0) (i : ℕ) :
    VarsIn (S.getD i zero).poly (· ∈ U) ∧ IsNat (S.getD i zero).poly := by
  by_cases hi : i < S.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact ⟨varsIn_of_mem hS _ (List.getElem_mem hi), isNat_of_mem hS _ (List.getElem_mem hi)⟩
  · rw [List.getD_eq_default _ _ (by omega), hzero]
    exact ⟨VarsIn.C _ _, IsNat.C_of_nonneg le_rfl⟩

theorem subBranches_specE (hpow : PowerSpec τ .hierarchical) (P : Program) (zero : Ex)
    (hzero : zero.poly = C 0) (S N : List Ex) :
    ∀ (rest : List Instr) (i : ℕ) (U : Set ℕ) (s : State),
      (∀ e ∈ S, ∃ c ∈ U, e.poly = X c) → (∀ e ∈ N, ∃ c ∈ U, e.poly = X c) →
      rest = P.drop i → (∀ j ∈ U, j < s.next) →
      SpecE ((subBranches zero S N i rest s).1.1.map (NForm.toFormula τ)) U s.next
        (subBranches zero S N i rest s).2.next (vwSet (subBranches zero S N i rest s).1.2)
        (subRel P zero S N (subBranches zero S N i rest s).1.2)
  | [], i, U, s, _, _, _, hs => by
    exact ((SpecE.nil U s.next).congr fun x => by simp [subRel, subBranches]).of_eq
      (by simp [subBranches]) (by ext c; simp [vwSet, subBranches])
  | .dec j x y :: rest, i, U, s, hS, hN, hP, hs => by
    have hPi : P[i]? = some (.dec j x y) := by rw [← List.head?_drop, ← hP]; rfl
    have hrest : rest = P.drop (i + 1) := by rw [← List.tail_drop, ← hP]; rfl
    have hreg : decReg P i = j := by simp [decReg, hPi]
    set s₁ := (fresh s).2
    set s₂ := (fresh s₁).2
    set V := (fresh s).1
    set W := (fresh s₁).1
    have hV : V.poly = X s.next := rfl
    have hW : W.poly = X (s.next + 1) := by simp [W, fresh_apply_poly, s₁, fresh_apply_next]
    have hs₂ : s₂.next = s.next + 2 := by simp [s₂, s₁, fresh_apply_next]
    set U₂ : Set ℕ := U ∪ {c | s.next ≤ c ∧ c < s.next + 2}
    have hU₂ : ∀ c ∈ U₂, c < s₂.next := by
      intro c hc; rcases hc with hc | hc
      · have := hs c hc; omega
      · rw [hs₂]; exact hc.2
    have hVU : s.next ∈ U₂ := Or.inr ⟨le_rfl, by omega⟩
    have hWU : s.next + 1 ∈ U₂ := Or.inr ⟨by omega, by omega⟩
    have hS₂ : ∀ e ∈ S, ∃ c ∈ U₂, e.poly = X c := fun e he => by
      obtain ⟨c, hc, h⟩ := hS e he; exact ⟨c, Or.inl hc, h⟩
    have hN₂ : ∀ e ∈ N, ∃ c ∈ U₂, e.poly = X c := fun e he => by
      obtain ⟨c, hc, h⟩ := hN e he; exact ⟨c, Or.inl hc, h⟩
    obtain ⟨hSv, hSn⟩ := getD_vars hS₂ hzero i
    obtain ⟨hNv, hNn⟩ := getD_vars hN₂ hzero j
    have hB := (MSpecL.seqM (τ := τ) (U := U₂) (ms := [bitAnd .hierarchical V (S.getD i zero)
        (N.getD j zero), do pure (.eq (S.getD i zero) (← addL [V, W]))])
      (Rs := [fun x => nv x V.poly = Nat.land (nv x (S.getD i zero).poly)
        (nv x (N.getD j zero).poly),
        fun x => zv x (S.getD i zero).poly = zv x V.poly + zv x W.poly]) (.cons
        (bitAnd_spec hpow (by rw [hV]; exact VarsIn.X hVU) hSv hNv (by rw [hV]; exact IsNat.X _)
          hSn hNn rfl rfl rfl)
        (.cons (MSpec.expr_bind (IsExpr.addL _) fun e he => (MSpec.eq' (U := U₂) rfl he hSv
          (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hV, hW]
              exact (VarsIn.X hVU).add (VarsIn.X hWU))).congr fun x => by simp) .nil))) s₂ hU₂
    set s₃ := (seqM [bitAnd .hierarchical V (S.getD i zero) (N.getD j zero),
      do pure (.eq (S.getD i zero) (← addL [V, W]))] s₂).2
    have hC := subBranches_specE hpow P zero hzero S N rest (i + 1) U₂ s₃ hS₂ hN₂ hrest
      fun c hc => lt_of_lt_of_le (hU₂ c hc) hB.le
    have hA : SpecE [] U s.next s₂.next {c | s.next ≤ c ∧ c < s.next + 2} fun _ => True := by
      rw [hs₂]; exact SpecE.expose U s.next 2
    have := hA.append ((SpecE.ofSpecL hB).append (by simpa using hC) hU₂) hs
    refine (this.of_eq ?_ ?_).congr fun x => ?_
    · simp [subBranches, s₃, s₂, s₁, V, W]
    · ext c
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.empty_union, vwSet, subBranches,
        NM.bind_apply, NM.pure_apply, List.mem_cons, exists_eq_or_imp, fresh_apply_poly,
        fresh_apply_next]
      constructor
      · rintro (h | h)
        · left
          rcases (show c = s.next ∨ c = s.next + 1 by omega) with rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr rfl
        · right; exact h
      · rintro (h | h)
        · left
          rcases h with h | h
          · have := X_injective h; omega
          · have := X_injective h; omega
        · right; exact h
    · simp [subRel, subBranches, hreg, s₃, s₂, s₁, V, W]
  | .inc j x :: rest, i, U, s, hS, hN, hP, hs => by
    have hrest : rest = P.drop (i + 1) := by rw [← List.tail_drop, ← hP]; rfl
    exact subBranches_specE hpow P zero hzero S N rest (i + 1) U s hS hN hrest hs
  | .halt :: rest, i, U, s, hS, hN, hP, hs => by
    have hrest : rest = P.drop (i + 1) := by rw [← List.tail_drop, ← hP]; rfl
    exact subBranches_specE hpow P zero hzero S N rest (i + 1) U s hS hN hrest hs

/-! ### Items 6 and 7 -/

theorem registerEq_spec (B Rj ιj : Ex) (decs incs : List Ex) {U : Set ℕ}
    (hB : VarsIn B.poly (· ∈ U)) (hR : VarsIn Rj.poly (· ∈ U)) (hι : VarsIn ιj.poly (· ∈ U))
    (hd : ∀ e ∈ decs, VarsIn e.poly (· ∈ U)) (hi : ∀ e ∈ incs, VarsIn e.poly (· ∈ U)) :
    MSpec τ (registerEq B Rj ιj decs incs) U fun x =>
      zv x Rj.poly + zv x B.poly * (decs.map fun e => zv x e.poly).sum =
        zv x ιj.poly + zv x B.poly * zv x Rj.poly + zv x B.poly * (incs.map fun e => zv x e.poly).sum := by
  unfold registerEq
  refine MSpec.expr_bind (IsExpr.addL _) fun e1 he1 => ?_
  refine MSpec.expr_bind (IsExpr.mulL _) fun e2 he2 => ?_
  refine MSpec.expr_bind (IsExpr.addL _) fun e3 he3 => ?_
  refine MSpec.expr_bind (IsExpr.mulL _) fun e4 he4 => ?_
  refine MSpec.expr_bind (IsExpr.addL _) fun e5 he5 => ?_
  refine MSpec.expr_bind (IsExpr.mulL _) fun e6 he6 => ?_
  refine MSpec.expr_bind (IsExpr.addL _) fun e7 he7 => ?_
  have hds : VarsIn (decs.map Ex.poly).sum (· ∈ U) := VarsIn.list_sum fun f hf => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hf; exact hd e he
  have his : VarsIn (incs.map Ex.poly).sum (· ∈ U) := VarsIn.list_sum fun f hf => by
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hf; exact hi e he
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons,
    List.sum_nil, mul_one, add_zero, he1, he2, he4, he5, he6] at he3 he7
  refine (MSpec.eq' (U := U) he3 he7 (hR.add (hB.mul hds))
    (hι.add ((hB.mul hR).add (hB.mul his)))).congr fun x => ?_
  simp only [zv_add, zv_mul, zv_list_sum, List.map_map, Function.comp_def]
  constructor <;> intro h <;> linear_combination h

theorem stateEq_spec (B Si e : Ex) (ins : List Ex) {U : Set ℕ}
    (hB : VarsIn B.poly (· ∈ U)) (hS : VarsIn Si.poly (· ∈ U)) (he : VarsIn e.poly (· ∈ U))
    (hi : ∀ f ∈ ins, VarsIn f.poly (· ∈ U)) :
    MSpec τ (stateEq B Si e ins) U fun x =>
      zv x Si.poly = zv x e.poly + zv x B.poly * (ins.map fun f => zv x f.poly).sum := by
  unfold stateEq
  refine MSpec.expr_bind (IsExpr.addL _) fun e1 he1 => ?_
  refine MSpec.expr_bind (IsExpr.mulL _) fun e2 he2 => ?_
  refine MSpec.expr_bind (IsExpr.addL _) fun e3 he3 => ?_
  have his : VarsIn (ins.map Ex.poly).sum (· ∈ U) := VarsIn.list_sum fun f hf => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf; exact hi g hg
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.sum_cons,
    List.sum_nil, mul_one, add_zero, he1, he2] at he3
  refine (MSpec.eq' (U := U) rfl he3 hS (he.add (hB.mul his))).congr fun x => ?_
  simp only [zv_add, zv_mul, zv_list_sum, List.map_map, Function.comp_def]

theorem items6_spec (p : Program) (r : ℕ) (a : List Ex) (zero B : Ex) (R S : List Ex)
    (vw : List (ℕ × Ex × Ex)) {U : Set ℕ} (hall : ∀ e : Ex, (e = zero ∨ e = B ∨ e ∈ a ∨ e ∈ R ∨
      e ∈ S ∨ ∃ v ∈ vw, e = v.2.1 ∨ e = v.2.2) → VarsIn e.poly (· ∈ U)) :
    MSpecL τ (items6 p r a zero B R S vw) U fun x => ∀ j ∈ List.range r,
      zv x (R.getD j zero).poly + zv x B.poly *
          ((decHandles p zero vw j).map fun e => zv x e.poly).sum =
        zv x (a.getD j zero).poly + zv x B.poly * zv x (R.getD j zero).poly +
          zv x B.poly * ((incHandles p zero S j).map fun e => zv x e.poly).sum := by
  have hget : ∀ (L : List Ex) (d : Ex) (j : ℕ), L.getD j d ∈ L ∨ L.getD j d = d := fun L d j => by
    by_cases hj : j < L.length
    · left; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    · right; rw [List.getD_eq_default _ _ (by omega)]
  have hlook : ∀ i, VarsIn (lookupVW zero vw i).1.poly (· ∈ U) ∧ VarsIn (lookupVW zero vw i).2.poly (· ∈ U) := by
    intro i
    unfold lookupVW
    cases h : vw.find? (fun e => e.1 == i) with
    | none => exact ⟨hall _ (Or.inl rfl), hall _ (Or.inl rfl)⟩
    | some v =>
      have hv := List.mem_of_find?_eq_some h
      exact ⟨hall _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨v, hv, Or.inl rfl⟩))))),
        hall _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨v, hv, Or.inr rfl⟩)))))⟩
  unfold items6
  refine MSpecL.seqM_map _ _ _ fun j _ => registerEq_spec _ _ _ _ _ (hall _ (by simp))
    ?_ ?_ ?_ ?_
  · rcases hget R zero j with h | h
    · exact hall _ (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · rw [h]; exact hall _ (Or.inl rfl)
  · rcases hget a zero j with h | h
    · exact hall _ (Or.inr (Or.inr (Or.inl h)))
    · rw [h]; exact hall _ (Or.inl rfl)
  · intro e he
    simp only [decHandles, List.mem_map] at he
    obtain ⟨i, -, rfl⟩ := he
    exact (hlook i).1
  · intro e he
    simp only [incHandles, List.mem_map] at he
    obtain ⟨i, -, rfl⟩ := he
    rcases hget S zero i with h | h
    · exact hall _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · rw [h]; exact hall _ (Or.inl rfl)

theorem items7_spec (p : Program) (zero one B : Ex) (S : List Ex) (vw : List (ℕ × Ex × Ex))
    {U : Set ℕ} (hall : ∀ e : Ex, (e = zero ∨ e = one ∨ e = B ∨ e ∈ S ∨
      ∃ v ∈ vw, e = v.2.1 ∨ e = v.2.2) → VarsIn e.poly (· ∈ U)) :
    MSpecL τ (items7 p zero one B S vw) U fun x => ∀ i ∈ List.range p.length,
      zv x (S.getD i zero).poly = zv x (if i = 0 then one else zero).poly +
        zv x B.poly * ((inHandles p zero S vw i).map fun e => zv x e.poly).sum := by
  have hget : ∀ (L : List Ex) (d : Ex) (j : ℕ), L.getD j d ∈ L ∨ L.getD j d = d := fun L d j => by
    by_cases hj : j < L.length
    · left; rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    · right; rw [List.getD_eq_default _ _ (by omega)]
  have hlook : ∀ i, VarsIn (lookupVW zero vw i).1.poly (· ∈ U) ∧ VarsIn (lookupVW zero vw i).2.poly (· ∈ U) := by
    intro i
    unfold lookupVW
    cases h : vw.find? (fun e => e.1 == i) with
    | none => exact ⟨hall _ (Or.inl rfl), hall _ (Or.inl rfl)⟩
    | some v =>
      have hv := List.mem_of_find?_eq_some h
      exact ⟨hall _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨v, hv, Or.inl rfl⟩)))),
        hall _ (Or.inr (Or.inr (Or.inr (Or.inr ⟨v, hv, Or.inr rfl⟩))))⟩
  have hS : ∀ i, VarsIn (S.getD i zero).poly (· ∈ U) := fun i => by
    rcases hget S zero i with h | h
    · exact hall _ (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · rw [h]; exact hall _ (Or.inl rfl)
  unfold items7
  refine MSpecL.seqM_map _ _ _ fun i _ => stateEq_spec _ _ _ _ (hall _ (by simp)) (hS i)
    ?_ ?_
  · split_ifs
    · exact hall _ (by simp)
    · exact hall _ (by simp)
  · intro e he
    simp only [inHandles, List.mem_flatMap, List.mem_append] at he
    obtain ⟨i', -, he⟩ := he
    rcases he with (he | he) | he
    · split_ifs at he
      · simp at he; rw [he]; exact hS i'
      · simp at he
    · split_ifs at he
      · simp at he; rw [he]; exact (hlook i').1
      · simp at he
    · split_ifs at he
      · simp at he; rw [he]; exact (hlook i').2
      · simp at he

/-! ### The shape of the branch histories -/

/-- The indices of the sub instructions of `p_i, p_{i+1}, …`. -/
def decIdx : List Instr → ℕ → List ℕ
  | [], _ => []
  | .dec _ _ _ :: rest, i => i :: decIdx rest (i + 1)
  | _ :: rest, i => decIdx rest (i + 1)

theorem subBranches_shape (zero : Ex) (S N : List Ex) :
    ∀ (rest : List Instr) (i : ℕ) (s : State),
      (∀ e ∈ (subBranches zero S N i rest s).1.2, ∃ c, e.2.1.poly = X c ∧
        e.2.2.poly = X (c + 1) ∧ s.next ≤ c ∧ c + 2 ≤ (subBranches zero S N i rest s).2.next) ∧
      (subBranches zero S N i rest s).1.2.map (·.1) = decIdx rest i ∧
      (subBranches zero S N i rest s).1.2.Pairwise fun e e' =>
        ∀ c c', e.2.1.poly = X c → e'.2.1.poly = X c' → c + 2 ≤ c'
  | [], i, s => by simp [subBranches, decIdx]
  | .dec j x y :: rest, i, s => by
    obtain ⟨h1, h2, h3⟩ := subBranches_shape zero S N rest (i + 1)
      (seqM [bitAnd .hierarchical (fresh s).1 (S.getD i zero) (N.getD j zero),
        do pure (.eq (S.getD i zero) (← addL [(fresh s).1, (fresh (fresh s).2).1]))]
        (fresh (fresh s).2).2).2
    have hle : (fresh (fresh s).2).2.next ≤ (seqM [bitAnd .hierarchical (fresh s).1
        (S.getD i zero) (N.getD j zero), do pure (.eq (S.getD i zero)
        (← addL [(fresh s).1, (fresh (fresh s).2).1]))] (fresh (fresh s).2).2).2.next := by
      have := (Counts.seqM_cons (Counts.bitAnd (fresh s).1 (S.getD i zero) (N.getD j zero))
        (Counts.seqM_cons ((Counts.addL [(fresh s).1, (fresh (fresh s).2).1]).bind fun e =>
          Counts.pure (NForm.eq (S.getD i zero) e)) Counts.seqM_nil) (fresh (fresh s).2).2).1
      omega
    have hn : (fresh (fresh s).2).2.next = s.next + 2 := by simp [fresh_apply_next]
    simp only [subBranches, NM.bind_apply, NM.pure_apply, List.mem_cons, forall_eq_or_imp,
      List.map_cons, decIdx, List.pairwise_cons]
    refine ⟨⟨⟨s.next, by simp [fresh_apply_poly], by simp [fresh_apply_poly, fresh_apply_next],
      le_rfl, ?_⟩, fun e he => ?_⟩, by rw [h2], ?_, h3⟩
    · have hm := (counts_subBranches zero S N (i + 1) rest (seqM [bitAnd .hierarchical (fresh s).1
        (S.getD i zero) (N.getD j zero), do pure (.eq (S.getD i zero)
        (← addL [(fresh s).1, (fresh (fresh s).2).1]))] (fresh (fresh s).2).2).2).1
      omega
    · obtain ⟨c, hc1, hc2, hc3, hc4⟩ := h1 e he
      exact ⟨c, hc1, hc2, by omega, hc4⟩
    · intro e he c c' hc hc'
      obtain ⟨c'', hc1, -, hc3, -⟩ := h1 e he
      simp only [fresh_apply_poly] at hc
      rw [hc1] at hc'
      have e1 := X_injective hc
      have e2 := X_injective hc'
      omega
  | .inc j x :: rest, i, s => subBranches_shape zero S N rest (i + 1) s
  | .halt :: rest, i, s => subBranches_shape zero S N rest (i + 1) s

/-! ### All items -/

/-- The state after items 1–4. -/
def stateAfter4 (p : Program) (r : ℕ) (a : List Ex) (zero one q c K B T F D : Ex)
    (R N S : List Ex) (s : State) : State :=
  (items4 r zero K D T F R N ((items3 F S ((items2 zero one K B T F D S
    ((items1 p a zero q c K B T s).2)).2)).2)).2

/-- The branch histories produced by the packed construction. -/
def packedVW (p : Program) (r : ℕ) (a : List Ex) (zero one q c K B T F D : Ex)
    (R N S : List Ex) (s : State) : List (ℕ × Ex × Ex) :=
  (subBranches zero S N 0 p (stateAfter4 p r a zero one q c K B T F D R N S s)).1.2

theorem SpecE.appendM_L {m₁ m₂ : NM (List NForm)} {s : State} {U E : Set ℕ}
    {R₁ R₂ : (ℕ → ℕ) → Prop}
    (h₁ : SpecL ((m₁ s).1.map (NForm.toFormula τ)) U s.next (m₁ s).2.next R₁)
    (h₂ : SpecE ((m₂ (m₁ s).2).1.map (NForm.toFormula τ)) U (m₁ s).2.next
      (m₂ (m₁ s).2).2.next E R₂) (hU : ∀ i ∈ U, i < s.next) :
    SpecE ((Packed.appendM m₁ m₂ s).1.map (NForm.toFormula τ)) U s.next
      (Packed.appendM m₁ m₂ s).2.next E fun x => R₁ x ∧ R₂ x := by
  have := (SpecE.ofSpecL h₁).append (by simpa using h₂) hU
  exact (this.of_eq (by simp [Packed.appendM]) (by simp)).of_eq rfl rfl

theorem packedFormulas_specE (hpow : PowerSpec τ .hierarchical) (p : Program) (r : ℕ)
    (a : List Ex) (zero one q c K B T F D : Ex) (R N S : List Ex) (s : State) {U : Set ℕ}
    {pq pc pK pB pT pF pD pR pN : ℕ} (hz : zero.poly = C 0) (ho : one.poly = C 1)
    (hq : q.poly = X pq) (hc : c.poly = X pc) (hK : K.poly = X pK) (hB : B.poly = X pB)
    (hT : T.poly = X pT) (hF : F.poly = X pF) (hD : D.poly = X pD)
    (hR : ∀ j < r, (R.getD j zero).poly = X (pR + j))
    (hN : ∀ j < r, (N.getD j zero).poly = X (pN + j))
    (hRm : ∀ e ∈ R, ∃ i ∈ U, e.poly = X i) (hNm : ∀ e ∈ N, ∃ i ∈ U, e.poly = X i)
    (hSm : ∀ e ∈ S, ∃ i ∈ U, e.poly = X i) (ha : ∀ e ∈ a, ∃ i ∈ U, e.poly = X i)
    (hpos : pq ∈ U ∧ pc ∈ U ∧ pK ∈ U ∧ pB ∈ U ∧ pT ∈ U ∧ pF ∈ U ∧ pD ∈ U)
    (hRU : ∀ j < r, pR + j ∈ U) (hNU : ∀ j < r, pN + j ∈ U) (hs : ∀ i ∈ U, i < s.next) :
    SpecE ((packedFormulas p r a zero one q c K B T F D R N S s).1.map (NForm.toFormula τ)) U
      s.next (packedFormulas p r a zero one q c K B T F D R N S s).2.next
      (vwSet (packedVW p r a zero one q c K B T F D R N S s)) fun x =>
        ((0 < x pc ∧ x pK = 2 ^ x pc ∧ x pB = 4 * x pK ∧ p.length < x pB ∧ x pT = x pB ^ x pq) ∧
          ∀ e ∈ a, nv x e.poly < x pK) ∧
        (((x pB : ℤ) * x pF + 1 = x pF + x pB * x pT) ∧ ((x pD : ℤ) + x pF = x pK * x pF) ∧
          (S.map fun e => zv x e.poly).sum = x pF ∧ zv x (S.getLastD zero).poly = x pT) ∧
        (∀ e ∈ S, Nat.land (nv x e.poly) (x pF) = nv x e.poly) ∧
        (∀ j < r, Nat.land (x (pR + j)) (x pD) = x (pR + j) ∧ x (pR + j) < x pT ∧
          x pK * x (pN + j) = Nat.land (x (pR + j) + x pD) (x pK * x pF)) ∧
        subRel p zero S N (packedVW p r a zero one q c K B T F D R N S s) x ∧
        (∀ j ∈ List.range r,
          zv x (R.getD j zero).poly + zv x B.poly *
              ((decHandles p zero (packedVW p r a zero one q c K B T F D R N S s) j).map
                fun e => zv x e.poly).sum =
            zv x (a.getD j zero).poly + zv x B.poly * zv x (R.getD j zero).poly +
              zv x B.poly * ((incHandles p zero S j).map fun e => zv x e.poly).sum) ∧
        (∀ i ∈ List.range p.length,
          zv x (S.getD i zero).poly = zv x (if i = 0 then one else zero).poly +
            zv x B.poly * ((inHandles p zero S
              (packedVW p r a zero one q c K B T F D R N S s) i).map fun e => zv x e.poly).sum) := by
  obtain ⟨hq', hc', hK', hB', hT', hF', hD'⟩ := hpos
  have h1 := items1_spec (τ := τ) hpow p a zero q c K B T hz hq hc hK hB hT
    ⟨hq', hc', hK', hB', hT'⟩ ha s hs
  set s1 := (items1 p a zero q c K B T s).2
  have hs1 : ∀ i ∈ U, i < s1.next := fun i hi => lt_of_lt_of_le (hs i hi) h1.le
  have h2 := items2_spec (τ := τ) zero one K B T F D S hz ho hK hB hT hF hD
    ⟨hK', hB', hT', hF', hD'⟩ hSm s1 hs1
  set s2 := (items2 zero one K B T F D S s1).2
  have hs2 : ∀ i ∈ U, i < s2.next := fun i hi => lt_of_lt_of_le (hs1 i hi) h2.le
  have h3 := items3_spec (τ := τ) hpow F S hF hF' hSm s2 hs2
  set s3 := (items3 F S s2).2
  have hs3 : ∀ i ∈ U, i < s3.next := fun i hi => lt_of_lt_of_le (hs2 i hi) h3.le
  have h4 := items4_spec (τ := τ) hpow r zero K D T F R N hK hD hT hF hR hN
    ⟨hK', hD', hT', hF'⟩ hRU hNU s3 hs3
  set s4 := (items4 r zero K D T F R N s3).2
  have hs4 : ∀ i ∈ U, i < s4.next := fun i hi => lt_of_lt_of_le (hs3 i hi) h4.le
  have h5 := subBranches_specE (τ := τ) hpow p zero hz S N p 0 U s4 hSm hNm (by simp) hs4
  set sb := subBranches zero S N 0 p s4
  have hvw : packedVW p r a zero one q c K B T F D R N S s = sb.1.2 := rfl
  have hs5 : ∀ i ∈ U ∪ vwSet sb.1.2, i < sb.2.next := by
    intro i hi
    rcases hi with hi | hi
    · exact lt_of_lt_of_le (hs4 i hi) h5.le
    · exact (h5.exp i hi).2
  have hall6 : ∀ e : Ex, (e = zero ∨ e = B ∨ e ∈ a ∨ e ∈ R ∨ e ∈ S ∨
      ∃ v ∈ sb.1.2, e = v.2.1 ∨ e = v.2.2) → VarsIn e.poly (· ∈ U ∪ vwSet sb.1.2) := by
    intro e he
    rcases he with rfl | rfl | he | he | he | ⟨v, hv, he⟩
    · rw [hz]; exact VarsIn.C _ _
    · rw [hB]; exact VarsIn.X (Or.inl hB')
    · obtain ⟨i, hi, h⟩ := ha e he; rw [h]; exact VarsIn.X (Or.inl hi)
    · obtain ⟨i, hi, h⟩ := hRm e he; rw [h]; exact VarsIn.X (Or.inl hi)
    · obtain ⟨i, hi, h⟩ := hSm e he; rw [h]; exact VarsIn.X (Or.inl hi)
    · obtain ⟨c, hc1, hc2, -, -⟩ := (subBranches_shape zero S N p 0 s4).1 v hv
      rcases he with rfl | rfl
      · rw [hc1]; exact VarsIn.X (Or.inr ⟨v, hv, Or.inl hc1⟩)
      · rw [hc2]; exact VarsIn.X (Or.inr ⟨v, hv, Or.inr hc2⟩)
  have hall7 : ∀ e : Ex, (e = zero ∨ e = one ∨ e = B ∨ e ∈ S ∨
      ∃ v ∈ sb.1.2, e = v.2.1 ∨ e = v.2.2) → VarsIn e.poly (· ∈ U ∪ vwSet sb.1.2) := by
    intro e he
    rcases he with rfl | rfl | he | he | he
    · exact hall6 _ (Or.inl rfl)
    · rw [ho]; exact VarsIn.C _ _
    · exact hall6 _ (Or.inr (Or.inl he))
    · exact hall6 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl he)))))
    · exact hall6 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr he)))))
  have h67 := (MSpecL.appendM (items6_spec (τ := τ) p r a zero B R S sb.1.2 hall6)
    (items7_spec (τ := τ) p zero one B S sb.1.2 hall7)) sb.2 hs5
  have htail := h5.append (SpecE.ofSpecL h67) hs4
  rw [hvw]
  refine SpecE.appendM_L h1 (SpecE.appendM_L h2 (SpecE.appendM_L h3 (SpecE.appendM_L h4 ?_ hs3)
    hs2) hs1) hs
  refine (htail.of_eq ?_ ?_).congr fun x => Iff.rfl
  · simp only [Packed.appendM, NM.bind_apply, NM.pure_apply, List.map_append]; rfl
  · simp

end ZInQ.Compiler.Packed
