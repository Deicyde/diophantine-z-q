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

theorem freshN_getD_poly {n : ℕ} {s : State} {i : ℕ} (hi : i < n) :
    ((freshN n s).1.getD i exZero).poly = X (s.next + i) := by
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

theorem getLastD_mem_or (S : List Ex) : S.getLastD exZero ∈ S ∨ S.getLastD exZero = exZero := by
  cases S using List.reverseRecOn with
  | nil => right; rfl
  | append_singleton l e => left; simp

theorem items2_spec (one K B T F D : Ex) (S : List Ex) {U : Set ℕ} {pK pB pT pF pD : ℕ}
    (hone : one.poly = C 1) (hK : K.poly = X pK) (hB : B.poly = X pB) (hT : T.poly = X pT)
    (hF : F.poly = X pF) (hD : D.poly = X pD) (hpos : pK ∈ U ∧ pB ∈ U ∧ pT ∈ U ∧ pF ∈ U ∧ pD ∈ U)
    (hS : ∀ e ∈ S, ∃ i ∈ U, e.poly = X i) :
    MSpecL τ (items2 one K B T F D S) U fun x =>
      ((x pB : ℤ) * x pF + 1 = x pF + x pB * x pT) ∧ ((x pD : ℤ) + x pF = x pK * x pF) ∧
      (S.map fun e => zv x e.poly).sum = x pF ∧ zv x (S.getLastD exZero).poly = x pT := by
  obtain ⟨hK', hB', hT', hF', hD'⟩ := hpos
  have hX : ∀ {i}, i ∈ U → VarsIn (X i : Poly) (· ∈ U) := fun h => VarsIn.X h
  unfold items2
  refine (MSpecL.seqM (Rs := [fun x => (x pB : ℤ) * x pF + 1 = x pF + x pB * x pT,
    fun x => (x pD : ℤ) + x pF = x pK * x pF, fun x => (S.map fun e => zv x e.poly).sum = x pF,
    fun x => zv x (S.getLastD exZero).poly = x pT]) ?_).congr fun x => by simp
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
    rcases getLastD_mem_or S with h | h
    · exact varsIn_of_mem hS _ h
    · rw [h]; exact VarsIn.zero _

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

theorem items4_spec (hpow : PowerSpec τ .hierarchical) (r : ℕ) (K D T F : Ex) (R N : List Ex)
    {U : Set ℕ} {pK pD pT pF pR pN : ℕ} (hK : K.poly = X pK) (hD : D.poly = X pD)
    (hT : T.poly = X pT) (hF : F.poly = X pF)
    (hR : ∀ j < r, (R.getD j exZero).poly = X (pR + j))
    (hN : ∀ j < r, (N.getD j exZero).poly = X (pN + j))
    (hpos : pK ∈ U ∧ pD ∈ U ∧ pT ∈ U ∧ pF ∈ U) (hRU : ∀ j < r, pR + j ∈ U)
    (hNU : ∀ j < r, pN + j ∈ U) :
    MSpecL τ (items4 r K D T F R N) U fun x => ∀ j < r,
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
def subRel (P : Program) (S N : List Ex) (vw : List (ℕ × Ex × Ex)) (x : ℕ → ℕ) : Prop :=
  ∀ e ∈ vw, nv x e.2.1.poly = Nat.land (nv x (S.getD e.1 exZero).poly)
      (nv x (N.getD (decReg P e.1) exZero).poly) ∧
    zv x (S.getD e.1 exZero).poly = zv x e.2.1.poly + zv x e.2.2.poly

theorem getD_vars {S : List Ex} {U : Set ℕ} (hS : ∀ e ∈ S, ∃ i ∈ U, e.poly = X i) (i : ℕ) :
    VarsIn (S.getD i exZero).poly (· ∈ U) ∧ IsNat (S.getD i exZero).poly := by
  by_cases hi : i < S.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact ⟨varsIn_of_mem hS _ (List.getElem_mem hi), isNat_of_mem hS _ (List.getElem_mem hi)⟩
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ⟨VarsIn.zero _, fun x => by simp [exZero]⟩

theorem subBranches_specE (hpow : PowerSpec τ .hierarchical) (P : Program) (S N : List Ex) :
    ∀ (rest : List Instr) (i : ℕ) (U : Set ℕ) (s : State),
      (∀ e ∈ S, ∃ c ∈ U, e.poly = X c) → (∀ e ∈ N, ∃ c ∈ U, e.poly = X c) →
      rest = P.drop i → (∀ j ∈ U, j < s.next) →
      SpecE ((subBranches S N i rest s).1.1.map (NForm.toFormula τ)) U s.next
        (subBranches S N i rest s).2.next (vwSet (subBranches S N i rest s).1.2)
        (subRel P S N (subBranches S N i rest s).1.2)
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
    obtain ⟨hSv, hSn⟩ := getD_vars hS₂ i
    obtain ⟨hNv, hNn⟩ := getD_vars hN₂ j
    have hB := (MSpecL.seqM (τ := τ) (U := U₂) (ms := [bitAnd .hierarchical V (S.getD i exZero)
        (N.getD j exZero), do pure (.eq (S.getD i exZero) (← addL [V, W]))])
      (Rs := [fun x => nv x V.poly = Nat.land (nv x (S.getD i exZero).poly)
        (nv x (N.getD j exZero).poly),
        fun x => zv x (S.getD i exZero).poly = zv x V.poly + zv x W.poly]) (.cons
        (bitAnd_spec hpow (by rw [hV]; exact VarsIn.X hVU) hSv hNv (by rw [hV]; exact IsNat.X _)
          hSn hNn rfl rfl rfl)
        (.cons (MSpec.expr_bind (IsExpr.addL _) fun e he => (MSpec.eq' (U := U₂) rfl he hSv
          (by simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hV, hW]
              exact (VarsIn.X hVU).add (VarsIn.X hWU))).congr fun x => by simp) .nil))) s₂ hU₂
    set s₃ := (seqM [bitAnd .hierarchical V (S.getD i exZero) (N.getD j exZero),
      do pure (.eq (S.getD i exZero) (← addL [V, W]))] s₂).2
    have hC := subBranches_specE hpow P S N rest (i + 1) U₂ s₃ hS₂ hN₂ hrest
      fun c hc => lt_of_lt_of_le (hU₂ c hc) hB.le
    have hA : SpecE [] U s.next s₂.next {c | s.next ≤ c ∧ c < s.next + 2} fun _ => True := by
      rw [hs₂]; exact SpecE.expose U s.next 2
    have := hA.append ((SpecE.ofSpecL hB).append (by simpa using hC) hU₂) hs
    refine (this.of_eq ?_ ?_).congr fun x => ?_
    · simp [subBranches, s₃, s₂, s₁, V, W]
    · ext c
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.empty_union, vwSet, subBranches,
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
    exact subBranches_specE hpow P S N rest (i + 1) U s hS hN hrest hs
  | .halt :: rest, i, U, s, hS, hN, hP, hs => by
    have hrest : rest = P.drop (i + 1) := by rw [← List.tail_drop, ← hP]; rfl
    exact subBranches_specE hpow P S N rest (i + 1) U s hS hN hrest hs

end ZInQ.Compiler.Packed
