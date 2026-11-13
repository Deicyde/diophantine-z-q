import ZInQKernel.Compiler.Programs.Point
import ZInQKernel.Compiler.Programs.FieldSpec

/-!
# Point routines (specifications)

Blueprint: `compiler/natural/programs/ir-point-routines.md`.

Straight-line `ℤ[s]` code is handled through `FProg`: a list of pair assignments `d ← e`
executed with the temporaries from `W`; below `W` its result agrees with the functional
semantics `FProg.sem`. The doubling, addition and halving routines then compute exactly
`jdbl`, `jdblB`, `jaddB` and `jmul` of the decision program.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace ZInQ.Compiler.IR

open Precision JTriple

/-- Straight-line pair assignments followed by a continuation `c`. -/
def FProg.code (W : ℕ) : List (ℕ × FExpr) → ZStmt → ZStmt
  | [], c => c
  | (d, e) :: l, c => FExpr.assign d e W ;;; FProg.code W l c

/-- One pair assignment on environments. -/
def fstep (E : ℕ → ℤ) (d : ℕ) (e : FExpr) : ℕ → ℤ :=
  Function.update (Function.update E d (e.eval E).re) (d + 1) (e.eval E).im

/-- The functional semantics of straight-line pair assignments. -/
def FProg.sem : List (ℕ × FExpr) → (ℕ → ℤ) → (ℕ → ℤ)
  | [], E => E
  | (d, e) :: l, E => FProg.sem l (fstep E d e)

/-- Every assignment writes below `W` and reads below `W`. -/
def FProg.WF (W : ℕ) (l : List (ℕ × FExpr)) : Prop := ∀ de ∈ l, de.1 + 1 < W ∧ de.2.VarsBelow W

theorem FProg.sem_congr {W : ℕ} : ∀ {l : List (ℕ × FExpr)}, FProg.WF W l →
    ∀ {E₁ E₂ : ℕ → ℤ}, (∀ v < W, E₁ v = E₂ v) → ∀ v < W, FProg.sem l E₁ v = FProg.sem l E₂ v
  | [], _, _, _, h => h
  | (d, e) :: l, hl, E₁, E₂, h => by
    refine FProg.sem_congr (l := l) (fun de hde => hl de (List.mem_cons_of_mem _ hde)) ?_
    intro v hv
    have he := (hl (d, e) (by simp)).2
    have hev : e.eval E₁ = e.eval E₂ := FExpr.eval_congr (fun v hv => h v hv) he
    simp only [fstep, Function.update_apply, hev]
    split_ifs <;> simp [h v hv]

theorem FProg.code_spec (W : ℕ) : ∀ (l : List (ℕ × FExpr)), FProg.WF W l → ∀ E : ℕ → ℤ,
    ∃ E', (∀ v < W, E' v = FProg.sem l E v) ∧
      ∀ c o, ZBigStep c E' o → ZBigStep (FProg.code W l c) E o
  | [], _, E => ⟨E, fun _ _ => rfl, fun _ _ h => h⟩
  | (d, e) :: l, hl, E => by
    obtain ⟨hd, he⟩ := hl (d, e) (by simp)
    have hl' : FProg.WF W l := fun de hde => hl de (List.mem_cons_of_mem _ hde)
    obtain ⟨E₁, h₁, v₁, f₁⟩ := FExpr.assign_spec hd he E
    obtain ⟨E₂, a₂, c₂⟩ := FProg.code_spec W l hl' E₁
    refine ⟨E₂, fun v hv => ?_, fun c o h => ZBigStep.seqNormal h₁ (c₂ c o h)⟩
    rw [a₂ v hv]
    refine FProg.sem_congr hl' (fun u hu => ?_) v hv
    simp only [fstep, Function.update_apply]
    have hre : E₁ d = (e.eval E).re := by rw [← v₁]; rfl
    have him : E₁ (d + 1) = (e.eval E).im := by rw [← v₁]; rfl
    split_ifs with h1 h2
    · subst h1; exact him
    · subst h2; exact hre
    · exact f₁ u hu h2 h1

theorem FProg.sem_frame {T : ℕ} : ∀ {l : List (ℕ × FExpr)}, (∀ de ∈ l, T ≤ de.1) →
    ∀ (E : ℕ → ℤ) v, v < T → FProg.sem l E v = E v
  | [], _, _, _, _ => rfl
  | (d, e) :: l, hl, E, v, hv => by
    rw [FProg.sem, FProg.sem_frame (fun de hde => hl de (List.mem_cons_of_mem _ hde)) _ v hv]
    have := hl (d, e) (by simp)
    simp only [fstep]
    rw [Function.update_of_ne (by simp at this; omega), Function.update_of_ne (by simp at this; omega)]

/-! ### Copies and constants -/

theorem ptOf_ext {E E' : ℕ → ℤ} {p q : ℕ} (h : ∀ i < 6, E' (q + i) = E (p + i)) :
    ptOf E' q = ptOf E p := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  have h3 := h 3 (by omega); have h4 := h 4 (by omega); have h5 := h 5 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [ptOf, zsOf, JTriple.mk.injEq, QuadraticAlgebra.mk.injEq]
  refine ⟨⟨h0, h1⟩, ⟨h2, ?_⟩, ⟨h4, ?_⟩⟩
  · rw [show q + 2 + 1 = q + 3 by omega, show p + 2 + 1 = p + 3 by omega]; exact h3
  · rw [show q + 4 + 1 = q + 5 by omega, show p + 4 + 1 = p + 5 by omega]; exact h5

theorem copyPt_spec {q p : ℕ} (hqp : q = p ∨ q + 6 ≤ p ∨ p + 6 ≤ q) (E : ℕ → ℤ) :
    ∃ E', ZBigStep (copyPt q p) E (.normal E') ∧ ptOf E' q = ptOf E p ∧
      ∀ v, (v < q ∨ q + 5 < v) → E' v = E v := by
  refine ⟨_, zbigStep_execZ (by simp [copyPt, ZStmt.Plain]) E, ptOf_ext fun i hi => ?_,
    fun v hv => ?_⟩
  · simp only [copyPt]
    interval_cases i <;> (try simp only [Nat.add_zero]) <;> zexec_simp
  · simp only [copyPt]; zexec_simp

theorem setO_spec (q : ℕ) (E : ℕ → ℤ) : ∃ E', ZBigStep (setO q) E (.normal E') ∧
    ptOf E' q = jO ∧ ∀ v, (v < q ∨ q + 5 < v) → E' v = E v := by
  refine ⟨_, zbigStep_execZ (by simp [setO, ZStmt.Plain]) E, ?_, fun v hv => ?_⟩
  · simp only [setO, ptOf, zsOf, jO]; zexec_simp
    simp only [JTriple.mk.injEq]
    refine ⟨?_, ?_, ?_⟩ <;> ext <;> simp
  · simp only [setO]; zexec_simp


theorem zsOf_fstep_self (E : ℕ → ℤ) (d : ℕ) (e : FExpr) : zsOf (fstep E d e) d = e.eval E := by
  simp [zsOf, fstep, Function.update_apply]

theorem zsOf_fstep_ne (E : ℕ → ℤ) {d w : ℕ} (e : FExpr) (h : w + 1 < d ∨ d + 1 < w) :
    zsOf (fstep E d e) w = zsOf E w := by
  simp only [zsOf, fstep]
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

theorem zsOf_congr {E E' : ℕ → ℤ} {w : ℕ} (h0 : E' w = E w) (h1 : E' (w + 1) = E (w + 1)) :
    zsOf E' w = zsOf E w := by simp [zsOf, h0, h1]

theorem zs_two : (⟨2, 0⟩ : Zs) = 2 := by ext <;> rfl
theorem zs_three : (⟨3, 0⟩ : Zs) = 3 := by ext <;> rfl
theorem zs_four : (⟨4, 0⟩ : Zs) = 4 := by ext <;> rfl
theorem zs_eight : (⟨8, 0⟩ : Zs) = 8 := by ext <;> rfl
theorem zs_A : (⟨-11243, 7950⟩ : Zs) = Acoef := rfl

/-- Evaluating straight-line point code at the level of `ℤ[s]`. -/
macro "fsem_simp" : tactic => `(tactic| simp (disch := omega) only [FProg.sem, FExpr.eval,
    zsOf_fstep_self, zsOf_fstep_ne, fN, fA, zs_two, zs_three, zs_four, zs_eight, zs_A])

theorem setP0_spec {q T : ℕ} (hT : q + 5 < T) (E : ℕ → ℤ) :
    ∃ E', ZBigStep (setP0 q T) E (.normal E') ∧ ptOf E' q = P0J ∧
      ∀ v, (v < q ∨ q + 5 < v) → v ≠ T → E' v = E v := by
  obtain ⟨E₁, h₁, v₁, f₁⟩ := intConst_spec q 3282 T (by omega) E
  obtain ⟨E₂, h₂, v₂, f₂⟩ := intConst_spec (q + 1) (-2320) T (by omega) E₁
  obtain ⟨E₃, h₃, v₃, f₃⟩ := intConst_spec (q + 2) (-247440) T (by omega) E₂
  obtain ⟨E₄, h₄, v₄, f₄⟩ := intConst_spec (q + 3) 174966 T (by omega) E₃
  obtain ⟨E₅, h₅, v₅, f₅⟩ := intConst_spec (q + 4) 4 T (by omega) E₄
  obtain ⟨E₆, h₆, v₆, f₆⟩ := intConst_spec (q + 5) 0 T (by omega) E₅
  refine ⟨E₆, ZBigStep.seqNormal h₁ (ZBigStep.seqNormal h₂ (ZBigStep.seqNormal h₃
    (ZBigStep.seqNormal h₄ (ZBigStep.seqNormal h₅ h₆)))), ?_, fun v hv hvT => ?_⟩
  · simp only [ptOf, zsOf, P0J, JTriple.mk.injEq, QuadraticAlgebra.mk.injEq]
    rw [show q + 2 + 1 = q + 3 by omega, show q + 4 + 1 = q + 5 by omega]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [f₆ _ (by omega) (by omega), f₅ _ (by omega) (by omega), f₄ _ (by omega) (by omega),
        f₃ _ (by omega) (by omega), f₂ _ (by omega) (by omega), v₁]
    · rw [f₆ _ (by omega) (by omega), f₅ _ (by omega) (by omega), f₄ _ (by omega) (by omega),
        f₃ _ (by omega) (by omega), v₂]
    · rw [f₆ _ (by omega) (by omega), f₅ _ (by omega) (by omega), f₄ _ (by omega) (by omega), v₃]
    · rw [f₆ _ (by omega) (by omega), f₅ _ (by omega) (by omega), v₄]
    · rw [f₆ _ (by omega) (by omega), v₅]
    · exact v₆
  · rw [f₆ _ (by omega) hvT, f₅ _ (by omega) hvT, f₄ _ (by omega) hvT, f₃ _ (by omega) hvT,
      f₂ _ (by omega) hvT, f₁ _ (by omega) hvT]

/-- The program list of the doubling. -/
def jdblList (p T : ℕ) : List (ℕ × FExpr) :=
  let X := FExpr.var p
  let Y := FExpr.var (p + 2)
  let Z := FExpr.var (p + 4)
  let M := FExpr.var T
  let S := FExpr.var (T + 2)
  let X3 := FExpr.var (T + 4)
  [(T, .add (.mul (fN 3) (.mul X X)) (.mul fA (.mul (.mul Z Z) (.mul Z Z)))),
   (T + 2, .mul (.mul (fN 4) X) (.mul Y Y)),
   (T + 4, .sub (.mul M M) (.mul (fN 2) S)),
   (T + 6, .sub (.mul M (.sub S X3)) (.mul (fN 8) (.mul (.mul Y Y) (.mul Y Y)))),
   (T + 8, .mul (.mul (fN 2) Y) Z)]

theorem jdblCode_eq (p q T : ℕ) : jdblCode p q T = FProg.code (T + 10) (jdblList p T) (copyPt q (T + 4)) :=
  rfl

theorem jdblCode_spec {p q T : ℕ} (hp : p + 5 < T) (hq : q + 5 < T) (E : ℕ → ℤ) :
    ∃ E', ZBigStep (jdblCode p q T) E (.normal E') ∧ ptOf E' q = jdbl Acoef (ptOf E p) ∧
      ∀ v < T, (v < q ∨ q + 5 < v) → E' v = E v := by
  have wf : FProg.WF (T + 10) (jdblList p T) := by
    intro de hde
    simp only [jdblList, List.mem_cons, List.mem_nil_iff, or_false] at hde
    rcases hde with rfl | rfl | rfl | rfl | rfl <;>
      simp [FExpr.VarsBelow, fN, fA] <;> omega
  obtain ⟨E₁, a₁, c₁⟩ := FProg.code_spec (T + 10) (jdblList p T) wf E
  obtain ⟨E₂, h₂, v₂, f₂⟩ := copyPt_spec (q := q) (p := T + 4) (by omega) E₁
  refine ⟨E₂, by rw [jdblCode_eq]; exact c₁ _ _ h₂, ?_, fun v hv hvq => ?_⟩
  · rw [v₂]
    have e : ∀ w, w + 1 < T + 10 → zsOf E₁ w = zsOf (FProg.sem (jdblList p T) E) w :=
      fun w hw => zsOf_congr (a₁ w (by omega)) (a₁ (w + 1) hw)
    simp only [ptOf]
    rw [e _ (by omega), e _ (by omega), e _ (by omega)]
    simp only [jdblList]
    fsem_simp
    simp only [jdbl, ptOf]
    ext <;> ring
  · rw [f₂ v hvq, a₁ v (by omega), FProg.sem_frame (T := T) _ E v hv]
    intro de hde
    simp only [jdblList, List.mem_cons, List.mem_nil_iff, or_false] at hde
    rcases hde with rfl | rfl | rfl | rfl | rfl <;> simp


theorem ptOf_congr {E E' : ℕ → ℤ} {p : ℕ} (h : ∀ i < 6, E' (p + i) = E (p + i)) :
    ptOf E' p = ptOf E p := ptOf_ext h

theorem jdblBCode_spec {p q T : ℕ} (hp : p + 5 < T) (hq : q + 5 < T) (E : ℕ → ℤ) :
    ∃ E', ZBigStep (jdblBCode p q T) E (.normal E') ∧ ptOf E' q = jdblB Acoef (ptOf E p) ∧
      ∀ v < T, (v < q ∨ q + 5 < v) → E' v = E v := by
  obtain ⟨E₁, h₁, v₁, f₁⟩ := zeroFlag_spec (f := T) (w := p + 4) (T := T + 1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ E
  obtain ⟨E₂, h₂, v₂, f₂⟩ := zeroFlag_spec (f := T + 1) (w := p + 2) (T := T + 2) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ E₁
  have hY : zsOf E₁ (p + 2) = zsOf E (p + 2) :=
    zsOf_congr (f₁ _ (by omega) (by omega)) (f₁ _ (by omega) (by omega))
  rw [hY] at v₂
  have hT : E₂ T = E₁ T := f₂ T (by omega) (by omega)
  set E₄ := Function.update (Function.update E₂ T (ZOp.eval E₂ (.nadd T (T + 1)))) (T + 1)
    (ZOp.eval (Function.update E₂ T (ZOp.eval E₂ (.nadd T (T + 1)))) (.const 0)) with hE₄
  have fr : ∀ v < T, E₄ v = E v := fun v hv => by
    rw [hE₄, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      f₂ v (by omega) (by omega), f₁ v (by omega) (by omega)]
  have hP : ptOf E₄ p = ptOf E p := ptOf_congr fun i hi => fr _ (by omega)
  have pre : ∀ {o}, ZBigStep (.ite (.neq T (T + 1)) (jdblCode p q (T + 2)) (setO q)) E₄ o →
      ZBigStep (jdblBCode p q T) E o := fun h =>
    ZBigStep.seqNormal h₁ (ZBigStep.seqNormal h₂ (ZBigStep.seqNormal (ZBigStep.assign _ _ _)
      (ZBigStep.seqNormal (ZBigStep.assign _ _ _) h)))
  have e4T : E₄ T = ((Int.natAbs (if zsOf E (p + 4) = 0 then 1 else 0) +
      Int.natAbs (if zsOf E (p + 2) = 0 then 1 else 0) : ℕ) : ℤ) := by
    rw [hE₄, Function.update_of_ne (by omega)]; simp [ZOp.eval, hT, v₁, v₂]
  have e41 : E₄ (T + 1) = 0 := by rw [hE₄]; simp [ZOp.eval]
  by_cases hc : (ptOf E p).Z = 0 ∨ (ptOf E p).Y = 0
  · have hc' : ¬ (E₄ T).natAbs = (E₄ (T + 1)).natAbs := by
      rw [e4T, e41]; simp only [ptOf] at hc
      by_cases h1 : zsOf E (p + 4) = 0 <;> by_cases h2 : zsOf E (p + 2) = 0 <;> simp_all
    obtain ⟨E₅, h₅, v₅, f₅⟩ := setO_spec q E₄
    refine ⟨E₅, pre (ZBigStep.iteFalse hc' h₅), ?_, fun v hv hvq => ?_⟩
    · rw [v₅, jdblB, ite_eq_left hc]
    · rw [f₅ v hvq, fr v hv]
  · have hc' : (E₄ T).natAbs = (E₄ (T + 1)).natAbs := by
      rw [e4T, e41]; simp only [ptOf, not_or] at hc; simp [hc.1, hc.2]
    obtain ⟨E₅, h₅, v₅, f₅⟩ := jdblCode_spec (p := p) (q := q) (T := T + 2) (by omega) (by omega) E₄
    refine ⟨E₅, pre (ZBigStep.iteTrue hc' h₅), ?_, fun v hv hvq => ?_⟩
    · rw [v₅, hP, jdblB, ite_eq_right hc]
    · rw [f₅ v (by omega) hvq, fr v hv]


/-- Branch on the zero flag of a pair, with a register `z` holding zero. -/
theorem zeroIte_spec' {f w t z : ℕ} (hft : f ≠ t) (hfw : f ≠ w ∧ f ≠ w + 1)
    (htw : t ≠ w ∧ t ≠ w + 1) (hfz : f ≠ z) (htz : t ≠ z) (S₁ S₂ : ZStmt) (E : ℕ → ℤ)
    (hz : E z = 0) :
    ∃ E₁, (∀ v, v ≠ f → v ≠ t → E₁ v = E v) ∧ ∀ o,
      (if zsOf E w = 0 then ZBigStep S₂ E₁ o else ZBigStep S₁ E₁ o) →
        ZBigStep (zeroFlag f w t ;;; .ite (.neq f z) S₁ S₂) E o := by
  obtain ⟨E₁, h₁, v₁, f₁⟩ := zeroFlag_spec hft hfw htw E
  refine ⟨E₁, f₁, fun o ho => ?_⟩
  have hz₁ : E₁ z = 0 := by rw [f₁ z (Ne.symm hfz) (Ne.symm htz), hz]
  by_cases hw : zsOf E w = 0
  · rw [ite_eq_left hw] at ho v₁
    exact ZBigStep.seqNormal h₁ (ZBigStep.iteFalse (by simp [ZCond.Holds, v₁, hz₁]) ho)
  · rw [ite_eq_right hw] at ho v₁
    exact ZBigStep.seqNormal h₁ (ZBigStep.iteTrue (by simp [ZCond.Holds, v₁, hz₁]) ho)

/-- Branch on the zero flag of a pair, setting the zero register first. -/
theorem zeroIte_spec {f w t : ℕ} (hft : f ≠ t) (hfw : f ≠ w ∧ f ≠ w + 1)
    (htw : t ≠ w ∧ t ≠ w + 1) (S₁ S₂ : ZStmt) (E : ℕ → ℤ) :
    ∃ E₁, (∀ v, v ≠ f → v ≠ t → E₁ v = E v) ∧ E₁ t = 0 ∧ ∀ o,
      (if zsOf E w = 0 then ZBigStep S₂ E₁ o else ZBigStep S₁ E₁ o) →
        ZBigStep (zeroFlag f w t ;;; .assign t (.const 0) ;;; .ite (.neq f t) S₁ S₂) E o := by
  obtain ⟨E₁, h₁, v₁, f₁⟩ := zeroFlag_spec hft hfw htw E
  set E₂ := Function.update E₁ t (ZOp.eval E₁ (.const 0)) with hE₂
  have e2t : E₂ t = 0 := by simp [hE₂, ZOp.eval]
  have e2f : E₂ f = E₁ f := by rw [hE₂, Function.update_of_ne hft]
  refine ⟨E₂, fun v h1 h2 => by rw [hE₂, Function.update_of_ne h2, f₁ v h1 h2], e2t,
    fun o ho => ?_⟩
  by_cases hw : zsOf E w = 0
  · rw [ite_eq_left hw] at ho v₁
    have hc : ¬ (ZCond.neq f t).Holds (Function.update E₁ t (ZOp.eval E₁ (.const 0))) := by
      simp only [ZCond.Holds]; rw [Function.update_of_ne hft, v₁]; simp [ZOp.eval]
    exact ZBigStep.seqNormal h₁ (ZBigStep.seqNormal (ZBigStep.assign _ _ _)
      (ZBigStep.iteFalse hc ho))
  · rw [ite_eq_right hw] at ho v₁
    have hc : (ZCond.neq f t).Holds (Function.update E₁ t (ZOp.eval E₁ (.const 0))) := by
      simp only [ZCond.Holds]; rw [Function.update_of_ne hft, v₁]; simp [ZOp.eval]
    exact ZBigStep.seqNormal h₁ (ZBigStep.seqNormal (ZBigStep.assign _ _ _)
      (ZBigStep.iteTrue hc ho))

/-- The first part of the addition: `Z₁²`, `Z₂²`, `U₁`, `U₂`, `S₁`, `S₂`, `H`, `Λ`. -/
def jaddList1 (p q B : ℕ) : List (ℕ × FExpr) :=
  let X1 := FExpr.var p
  let Y1 := FExpr.var (p + 2)
  let Z1 := FExpr.var (p + 4)
  let X2 := FExpr.var q
  let Y2 := FExpr.var (q + 2)
  let Z2 := FExpr.var (q + 4)
  let Z1s := FExpr.var B
  let Z2s := FExpr.var (B + 2)
  let U1 := FExpr.var (B + 4)
  let U2 := FExpr.var (B + 6)
  let S1 := FExpr.var (B + 8)
  let S2 := FExpr.var (B + 10)
  [(B, .mul Z1 Z1), (B + 2, .mul Z2 Z2), (B + 4, .mul X1 Z2s), (B + 6, .mul X2 Z1s),
   (B + 8, .mul Y1 (.mul Z2s Z2)), (B + 10, .mul Y2 (.mul Z1s Z1)), (B + 12, .sub U2 U1),
   (B + 14, .sub S2 S1)]

/-- The second part of the addition: `H²`, `H³`, `X₃`, `Y₃`, `Z₃`. -/
def jaddList2 (p q B : ℕ) : List (ℕ × FExpr) :=
  let Z1 := FExpr.var (p + 4)
  let Z2 := FExpr.var (q + 4)
  let U1 := FExpr.var (B + 4)
  let S1 := FExpr.var (B + 8)
  let H := FExpr.var (B + 12)
  let L := FExpr.var (B + 14)
  let HH := FExpr.var (B + 19)
  let HHH := FExpr.var (B + 21)
  let X3 := FExpr.var (B + 23)
  [(B + 19, .mul H H), (B + 21, .mul HH H),
   (B + 23, .sub (.sub (.mul L L) HHH) (.mul (fN 2) (.mul U1 HH))),
   (B + 25, .sub (.mul L (.sub (.mul U1 HH) X3)) (.mul S1 HHH)),
   (B + 27, .mul (.mul H Z1) Z2)]

theorem jaddBCode_eq (p q r T : ℕ) : jaddBCode p q r T =
    (zeroFlag T (p + 4) (T + 1) ;;; .assign (T + 1) (.const 0) ;;; .ite (.neq T (T + 1))
      (zeroFlag (T + 2) (q + 4) (T + 1) ;;; .assign (T + 1) (.const 0) ;;;
        .ite (.neq (T + 2) (T + 1))
          (FProg.code (T + 3 + 29) (jaddList1 p q (T + 3))
            (zeroFlag (T + 3 + 16) (T + 3 + 12) (T + 3 + 17) ;;; .assign (T + 3 + 17) (.const 0) ;;;
              .ite (.neq (T + 3 + 16) (T + 3 + 17))
                (FProg.code (T + 3 + 29) (jaddList2 p q (T + 3)) (copyPt r (T + 3 + 23)))
                (zeroFlag (T + 3 + 18) (T + 3 + 14) (T + 3 + 19) ;;;
                  .ite (.neq (T + 3 + 18) (T + 3 + 17)) (setO r) (jdblBCode p r (T + 3 + 19)))))
          (copyPt r p))
      (copyPt r q)) := rfl


theorem jaddList1_wf (p q B : ℕ) (hp : p + 5 < B) (hq : q + 5 < B) :
    FProg.WF (B + 29) (jaddList1 p q B) := by
  intro de hde
  simp only [jaddList1, List.mem_cons, List.mem_nil_iff, or_false] at hde
  rcases hde with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [FExpr.VarsBelow] <;> omega

theorem jaddList2_wf (p q B : ℕ) (hp : p + 5 < B) (hq : q + 5 < B) :
    FProg.WF (B + 29) (jaddList2 p q B) := by
  intro de hde
  simp only [jaddList2, List.mem_cons, List.mem_nil_iff, or_false] at hde
  rcases hde with rfl | rfl | rfl | rfl | rfl <;> simp [FExpr.VarsBelow, fN] <;> omega

theorem jaddBCode_spec {p q r T : ℕ} (hp : p + 5 < T) (hq : q + 5 < T) (hr : r + 5 < T)
    (hrp : r = p ∨ r + 6 ≤ p ∨ p + 6 ≤ r) (hrq : r = q ∨ r + 6 ≤ q ∨ q + 6 ≤ r) (E : ℕ → ℤ) :
    ∃ E', ZBigStep (jaddBCode p q r T) E (.normal E') ∧
      ptOf E' r = jaddB Acoef (ptOf E p) (ptOf E q) ∧
      ∀ v < T, (v < r ∨ r + 5 < v) → E' v = E v := by
  rw [jaddBCode_eq]
  obtain ⟨E₁, f₁, -, run₁⟩ := zeroIte_spec (f := T) (w := p + 4) (t := T + 1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ _ (copyPt r q) E
  have g₁ : ∀ v < T, E₁ v = E v := fun v hv => f₁ v (by omega) (by omega)
  by_cases hPZ : zsOf E (p + 4) = 0
  · obtain ⟨E₂, h₂, v₂, f₂⟩ := copyPt_spec (q := r) (p := q) hrq E₁
    refine ⟨E₂, run₁ _ (by rw [ite_eq_left hPZ]; exact h₂), ?_, fun v hv hvr => ?_⟩
    · rw [v₂, ptOf_congr (fun i hi => g₁ _ (by omega)), jaddB, ite_eq_left (show (ptOf E p).Z = 0 from hPZ)]
    · rw [f₂ v hvr, g₁ v hv]
  obtain ⟨E₂, f₂, -, run₂⟩ := zeroIte_spec (f := T + 2) (w := q + 4) (t := T + 1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ _ (copyPt r p) E₁
  have g₂ : ∀ v < T, E₂ v = E v := fun v hv => by rw [f₂ v (by omega) (by omega), g₁ v hv]
  have hQ1 : zsOf E₁ (q + 4) = zsOf E (q + 4) := zsOf_congr (g₁ _ (by omega)) (g₁ _ (by omega))
  have hPZ' : ¬ (ptOf E p).Z = 0 := hPZ
  by_cases hQZ : zsOf E (q + 4) = 0
  · obtain ⟨E₃, h₃, v₃, f₃⟩ := copyPt_spec (q := r) (p := p) hrp E₂
    refine ⟨E₃, run₁ _ (by rw [ite_eq_right hPZ]; exact run₂ _ (by rw [hQ1, ite_eq_left hQZ]; exact h₃)), ?_,
      fun v hv hvr => ?_⟩
    · rw [v₃, ptOf_congr (fun i hi => g₂ _ (by omega)), jaddB, ite_eq_right hPZ',
        ite_eq_left (show (ptOf E q).Z = 0 from hQZ)]
    · rw [f₃ v hvr, g₂ v hv]
  have hQZ' : ¬ (ptOf E q).Z = 0 := hQZ
  -- the generic case
  have hE2 : ∀ w, w + 1 < T → zsOf E₂ w = zsOf E w :=
    fun w hw => zsOf_congr (g₂ w (by omega)) (g₂ (w + 1) hw)
  obtain ⟨E₃, a₃, c₃⟩ := FProg.code_spec (T + 3 + 29) (jaddList1 p q (T + 3))
    (jaddList1_wf p q (T + 3) (by omega) (by omega)) E₂
  have hE3 : ∀ w, w + 1 < T + 3 + 29 → zsOf E₃ w = zsOf (FProg.sem (jaddList1 p q (T + 3)) E₂) w :=
    fun w hw => zsOf_congr (a₃ w (by omega)) (a₃ (w + 1) hw)
  have g₃ : ∀ v < T, E₃ v = E v := fun v hv => by
    rw [a₃ v (by omega), FProg.sem_frame (T := T + 3) _ E₂ v (by omega), g₂ v hv]
    intro de hde
    simp only [jaddList1, List.mem_cons, List.mem_nil_iff, or_false] at hde
    rcases hde with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hH : zsOf E₃ (T + 3 + 12) = jH (ptOf E p) (ptOf E q) := by
    rw [hE3 _ (by omega)]
    simp (disch := omega) only [jaddList1, FProg.sem, FExpr.eval, zsOf_fstep_self, zsOf_fstep_ne,
      hE2]
    simp only [jH, ptOf]; ring
  have hL : zsOf E₃ (T + 3 + 14) = jΛ (ptOf E p) (ptOf E q) := by
    rw [hE3 _ (by omega)]
    simp (disch := omega) only [jaddList1, FProg.sem, FExpr.eval, zsOf_fstep_self, zsOf_fstep_ne,
      hE2]
    simp only [jΛ, ptOf]; ring
  obtain ⟨E₄, f₄, z₄, run₄⟩ := zeroIte_spec (f := T + 3 + 16) (w := T + 3 + 12) (t := T + 3 + 17)
    (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (FProg.code (T + 3 + 29) (jaddList2 p q (T + 3)) (copyPt r (T + 3 + 23)))
    (zeroFlag (T + 3 + 18) (T + 3 + 14) (T + 3 + 19) ;;;
      .ite (.neq (T + 3 + 18) (T + 3 + 17)) (setO r) (jdblBCode p r (T + 3 + 19))) E₃
  have hE4 : ∀ w, w + 1 < T + 3 + 16 → zsOf E₄ w = zsOf E₃ w :=
    fun w hw => zsOf_congr (f₄ w (by omega) (by omega)) (f₄ (w + 1) (by omega) (by omega))
  have g₄ : ∀ v < T, E₄ v = E v := fun v hv => by rw [f₄ v (by omega) (by omega), g₃ v hv]
  have pre : ∀ {o}, (if zsOf E₃ (T + 3 + 12) = 0 then
      ZBigStep (zeroFlag (T + 3 + 18) (T + 3 + 14) (T + 3 + 19) ;;;
        .ite (.neq (T + 3 + 18) (T + 3 + 17)) (setO r) (jdblBCode p r (T + 3 + 19))) E₄ o
      else ZBigStep (FProg.code (T + 3 + 29) (jaddList2 p q (T + 3)) (copyPt r (T + 3 + 23))) E₄ o) →
      ZBigStep _ E o := fun h =>
    run₁ _ (by rw [ite_eq_right hPZ]; exact run₂ _ (by rw [hQ1, ite_eq_right hQZ]; exact c₃ _ _ (run₄ _ h)))
  by_cases hHz : jH (ptOf E p) (ptOf E q) = 0
  · -- `H = 0`
    obtain ⟨E₅, f₅, run₅⟩ := zeroIte_spec' (f := T + 3 + 18) (w := T + 3 + 14) (t := T + 3 + 19)
      (z := T + 3 + 17) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) (by omega)
      (setO r) (jdblBCode p r (T + 3 + 19)) E₄ z₄
    have g₅ : ∀ v < T, E₅ v = E v := fun v hv => by rw [f₅ v (by omega) (by omega), g₄ v hv]
    have hL4 : zsOf E₄ (T + 3 + 14) = jΛ (ptOf E p) (ptOf E q) := by rw [hE4 _ (by omega), hL]
    by_cases hLz : jΛ (ptOf E p) (ptOf E q) = 0
    · obtain ⟨E₆, h₆, v₆, f₆⟩ := jdblBCode_spec (p := p) (q := r) (T := T + 3 + 19) (by omega)
        (by omega) E₅
      refine ⟨E₆, pre (by rw [hH, ite_eq_left hHz]; exact run₅ _ (by rw [hL4, ite_eq_left hLz]; exact h₆)),
        ?_, fun v hv hvr => ?_⟩
      · rw [v₆, ptOf_congr (fun i hi => g₅ _ (by omega)), jaddB, ite_eq_right hPZ', ite_eq_right hQZ',
          ite_eq_right (by simpa using hHz), ite_eq_left hLz]
      · rw [f₆ v (by omega) hvr, g₅ v hv]
    · obtain ⟨E₆, h₆, v₆, f₆⟩ := setO_spec r E₅
      refine ⟨E₆, pre (by rw [hH, ite_eq_left hHz]; exact run₅ _ (by rw [hL4, ite_eq_right hLz]; exact h₆)),
        ?_, fun v hv hvr => ?_⟩
      · rw [v₆, jaddB, ite_eq_right hPZ', ite_eq_right hQZ', ite_eq_right (by simpa using hHz), ite_eq_right hLz]
      · rw [f₆ v hvr, g₅ v hv]
  · -- `H ≠ 0`
    obtain ⟨E₅, a₅, c₅⟩ := FProg.code_spec (T + 3 + 29) (jaddList2 p q (T + 3))
      (jaddList2_wf p q (T + 3) (by omega) (by omega)) E₄
    obtain ⟨E₆, h₆, v₆, f₆⟩ := copyPt_spec (q := r) (p := T + 3 + 23) (by omega) E₅
    have hE5 : ∀ w, w + 1 < T + 3 + 29 →
        zsOf E₅ w = zsOf (FProg.sem (jaddList2 p q (T + 3)) E₄) w :=
      fun w hw => zsOf_congr (a₅ w (by omega)) (a₅ (w + 1) hw)
    refine ⟨E₆, pre (by rw [hH, ite_eq_right hHz]; exact c₅ _ _ h₆), ?_, fun v hv hvr => ?_⟩
    · rw [v₆, jaddB, ite_eq_right hPZ', ite_eq_right hQZ', ite_eq_left (by simpa using hHz)]
      simp only [ptOf]
      rw [hE5 _ (by omega), hE5 _ (by omega), hE5 _ (by omega)]
      simp (disch := omega) only [jaddList2, jaddList1, FProg.sem, FExpr.eval, zsOf_fstep_self,
        zsOf_fstep_ne, hE4, hE3, hE2, fN, zs_two]
      simp only [jadd, jH, jΛ, ptOf]
      ext <;> ring
    · rw [f₆ v hvr, a₅ v (by omega), FProg.sem_frame (T := T + 3) _ E₄ v (by omega), g₄ v hv]
      intro de hde
      simp only [jaddList2, List.mem_cons, List.mem_nil_iff, or_false] at hde
      rcases hde with rfl | rfl | rfl | rfl | rfl <;> simp


/-- The body of the halving loop. -/
def jmulBody (T : ℕ) : ZStmt :=
  .assign (T + 13) (.mod (T + 12) (T + 14)) ;;;
    .ite (.neq (T + 13) (T + 15)) (jaddBCode T (T + 6) T (T + 17)) .skip ;;;
    jdblBCode (T + 6) (T + 6) (T + 17) ;;;
    .assign (T + 12) (.div (T + 12) (T + 14))

theorem jmulCode_eq (k out T : ℕ) : jmulCode k out T =
    (.assign (T + 12) (.abs k) ;;; setO T ;;; setP0 (T + 6) (T + 17) ;;;
      .assign (T + 14) (.const 2) ;;; .assign (T + 15) (.const 1) ;;; .assign (T + 16) (.const 0) ;;;
      .loop (T + 16) (T + 12) (jmulBody T) ;;;
      .ite (.lt k (T + 16)) (.assign (T + 2) (.neg (T + 2)) ;;; .assign (T + 3) (.neg (T + 3)))
        .skip ;;;
      copyPt out T) := rfl

theorem jmulLoop_spec {T : ℕ} (E₀ : ℕ → ℤ) : ∀ (n : ℕ) (E : ℕ → ℤ), E (T + 12) = n →
    E (T + 14) = 2 → E (T + 15) = 1 → E (T + 16) = 0 → (∀ v < T, E v = E₀ v) →
    ∃ E', ZBigStep (.loop (T + 16) (T + 12) (jmulBody T)) E (.normal E') ∧
      ptOf E' T = jmulLoop Acoef (ptOf E T) (ptOf E (T + 6)) n ∧ E' (T + 16) = 0 ∧
      ∀ v < T, E' v = E₀ v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E he h14 h15 h16 hfr
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · refine ⟨E, ZBigStep.loopFalse (by simp [he, h16]), by rw [jmulLoop_zero], h16, hfr⟩
    -- one iteration
    set E₁ := Function.update E (T + 13) (ZOp.eval E (.mod (T + 12) (T + 14))) with hE₁
    have e13 : E₁ (T + 13) = ((n % 2 : ℕ) : ℤ) := by
      simp [hE₁, ZOp.eval, he, h14]
    have g₁ : ∀ v, v ≠ T + 13 → E₁ v = E v := fun v hv => Function.update_of_ne hv _ _
    have hA₁ : ptOf E₁ T = ptOf E T := ptOf_congr fun i hi => g₁ _ (by omega)
    have hB₁ : ptOf E₁ (T + 6) = ptOf E (T + 6) := ptOf_congr fun i hi => g₁ _ (by omega)
    -- the conditional addition
    obtain ⟨E₂, h₂, hA₂, hB₂, g₂⟩ : ∃ E₂, ZBigStep (.ite (.neq (T + 13) (T + 15))
        (jaddBCode T (T + 6) T (T + 17)) .skip) E₁ (.normal E₂) ∧
        ptOf E₂ T = (if n % 2 = 1 then jaddB Acoef (ptOf E T) (ptOf E (T + 6)) else ptOf E T) ∧
        ptOf E₂ (T + 6) = ptOf E (T + 6) ∧ ∀ v, (v < T ∨ T + 5 < v) → v < T + 17 → E₂ v = E₁ v := by
      by_cases hodd : n % 2 = 1
      · obtain ⟨E₂, h₂, v₂, f₂⟩ := jaddBCode_spec (p := T) (q := T + 6) (r := T) (T := T + 17)
          (by omega) (by omega) (by omega) (Or.inl rfl) (Or.inr (Or.inl (by omega))) E₁
        refine ⟨E₂, ZBigStep.iteTrue (by simp [ZCond.Holds, e13, hodd, g₁ (T + 15) (by omega),
          h15]) h₂, by rw [v₂, ite_eq_left hodd, hA₁, hB₁], ?_, fun v hv hv' => f₂ v hv' hv⟩
        rw [ptOf_congr (fun i hi => f₂ _ (by omega) (by omega)), hB₁]
      · have hc : ¬ (ZCond.neq (T + 13) (T + 15)).Holds E₁ := by
          simp [ZCond.Holds, e13, g₁ (T + 15) (by omega), h15]; omega
        exact ⟨E₁, ZBigStep.iteFalse hc (ZBigStep.skip _), by rw [ite_eq_right hodd, hA₁], hB₁,
          fun _ _ _ => rfl⟩
    -- the doubling
    obtain ⟨E₃, h₃, v₃, f₃⟩ := jdblBCode_spec (p := T + 6) (q := T + 6) (T := T + 17)
      (by omega) (by omega) E₂
    set E₄ := Function.update E₃ (T + 12) (ZOp.eval E₃ (.div (T + 12) (T + 14))) with hE₄
    have g23 : ∀ v, v < T ∨ T + 11 < v → v ≠ T + 13 → v < T + 17 → E₃ v = E v := by
      intro v hv h13 hv'
      rw [f₃ v hv' (by omega), g₂ v (by omega) hv', g₁ v h13]
    have g4 : ∀ v, v < T ∨ T + 12 < v → v ≠ T + 13 → v < T + 17 → E₄ v = E v :=
      fun v hv h13 hv' => by rw [hE₄, Function.update_of_ne (by omega), g23 v (by omega) h13 hv']
    have e12 : E₄ (T + 12) = ((n / 2 : ℕ) : ℤ) := by
      simp [hE₄, ZOp.eval, g23 (T + 12) (by omega) (by omega) (by omega), he,
        g23 (T + 14) (by omega) (by omega) (by omega), h14]
    have hA₄ : ptOf E₄ T = ptOf E₂ T := ptOf_congr fun i hi => by
      rw [hE₄, Function.update_of_ne (by omega), f₃ _ (by omega) (by omega)]
    have hB₄ : ptOf E₄ (T + 6) = jdblB Acoef (ptOf E (T + 6)) := by
      rw [ptOf_congr (fun i hi => by rw [hE₄, Function.update_of_ne (by omega)]) , v₃, hB₂]
    obtain ⟨E₅, h₅, v₅, z₅, f₅⟩ := ih (n / 2) (Nat.div_lt_self hn (by norm_num)) E₄ e12
      (by rw [g4 (T + 14) (by omega) (by omega) (by omega), h14])
      (by rw [g4 (T + 15) (by omega) (by omega) (by omega), h15])
      (by rw [g4 (T + 16) (by omega) (by omega) (by omega), h16])
      (fun v hv => by rw [g4 v (by omega) (by omega) (by omega), hfr v hv])
    have hcond : (E (T + 16)).natAbs < (E (T + 12)).natAbs := by rw [he, h16]; simp; omega
    refine ⟨E₅, ZBigStep.loopNormal hcond
      (ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.seqNormal h₂
        (ZBigStep.seqNormal h₃ (ZBigStep.assign _ _ _)))) h₅, ?_, z₅, f₅⟩
    rw [v₅, hA₄, hB₄, hA₂]
    exact (jmulLoop_of_ne_zero (e := n) _ _ _ (by omega)).symm


theorem jmulCode_spec {k out T : ℕ} (hk : k < T) (hout : out + 5 < T) (E : ℕ → ℤ) :
    ∃ E', ZBigStep (jmulCode k out T) E (.normal E') ∧ ptOf E' out = jmul (E k) ∧
      ∀ v < T, (v < out ∨ out + 5 < v) → E' v = E v := by
  rw [jmulCode_eq]
  set E₁ := Function.update E (T + 12) (ZOp.eval E (.abs k)) with hE₁
  obtain ⟨E₂, h₂, v₂, f₂⟩ := setO_spec T E₁
  obtain ⟨E₃, h₃, v₃, f₃⟩ := setP0_spec (q := T + 6) (T := T + 17) (by omega) E₂
  set E₆ := Function.update (Function.update (Function.update E₃ (T + 14) (ZOp.eval E₃ (.const 2)))
    (T + 15) (ZOp.eval (Function.update E₃ (T + 14) (ZOp.eval E₃ (.const 2))) (.const 1))) (T + 16)
    (ZOp.eval (Function.update (Function.update E₃ (T + 14) (ZOp.eval E₃ (.const 2)))
    (T + 15) (ZOp.eval (Function.update E₃ (T + 14) (ZOp.eval E₃ (.const 2))) (.const 1)))
      (.const 0)) with hE₆
  have g6 : ∀ v, v ≠ T + 14 → v ≠ T + 15 → v ≠ T + 16 → E₆ v = E₃ v := fun v h1 h2 h3 => by
    rw [hE₆, Function.update_of_ne h3, Function.update_of_ne h2, Function.update_of_ne h1]
  have g36 : ∀ v, (v < T ∨ T + 17 < v) → v ≠ T + 12 → v ≠ T + 14 → v ≠ T + 15 → v ≠ T + 16 →
      E₆ v = E v := fun v hv h12 h14 h15 h16 => by
    rw [g6 v h14 h15 h16, f₃ v (by omega) (by omega), f₂ v (by omega), hE₁,
      Function.update_of_ne h12]
  have e12 : E₆ (T + 12) = ((E k).natAbs : ℤ) := by
    rw [g6 _ (by omega) (by omega) (by omega), f₃ _ (by omega) (by omega), f₂ _ (by omega), hE₁]
    simp only [Function.update_self, ZOp.eval, Int.abs_eq_natAbs]
  have pA : ptOf E₆ T = jO := by
    rw [ptOf_congr (fun i hi => by rw [g6 _ (by omega) (by omega) (by omega),
      f₃ _ (by omega) (by omega)]), v₂]
  have pB : ptOf E₆ (T + 6) = P0J := by
    rw [ptOf_congr (fun i hi => g6 _ (by omega) (by omega) (by omega)), v₃]
  obtain ⟨E₇, h₇, v₇, z₇, f₇⟩ := jmulLoop_spec (T := T) E (E k).natAbs E₆ e12
    (by simp [hE₆, ZOp.eval]) (by rw [hE₆, Function.update_of_ne (by omega)]; simp [ZOp.eval])
    (by simp [hE₆, ZOp.eval]) (fun v hv => g36 v (by omega) (by omega) (by omega) (by omega) (by omega))
  rw [pA, pB] at v₇
  have hk7 : E₇ k = E k := f₇ k hk
  have pre : ∀ {E₈ o}, ZBigStep (.ite (.lt k (T + 16)) (.assign (T + 2) (.neg (T + 2)) ;;;
      .assign (T + 3) (.neg (T + 3))) .skip) E₇ (.normal E₈) → ZBigStep (copyPt out T) E₈ o →
      ZBigStep _ E o := fun h8 h9 =>
    ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.seqNormal h₂ (ZBigStep.seqNormal h₃
      (ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.seqNormal (ZBigStep.assign _ _ _)
      (ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.seqNormal h₇
      (ZBigStep.seqNormal h8 h9)))))))
  by_cases hneg : E k < 0
  · set E₈ := Function.update (Function.update E₇ (T + 2) (ZOp.eval E₇ (.neg (T + 2)))) (T + 3)
      (ZOp.eval (Function.update E₇ (T + 2) (ZOp.eval E₇ (.neg (T + 2)))) (.neg (T + 3))) with hE₈
    have h8 : ZBigStep (.ite (.lt k (T + 16)) (.assign (T + 2) (.neg (T + 2)) ;;;
        .assign (T + 3) (.neg (T + 3))) .skip) E₇ (.normal E₈) :=
      ZBigStep.iteTrue (by simp [ZCond.Holds, hk7, z₇, hneg])
        (ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.assign _ _ _))
    obtain ⟨E₉, h₉, v₉, f₉⟩ := copyPt_spec (q := out) (p := T) (by omega) E₈
    refine ⟨E₉, pre h8 h₉, ?_, fun v hv hvo => ?_⟩
    · rw [v₉]
      have : ptOf E₈ T = jneg (ptOf E₇ T) := by
        simp only [ptOf, zsOf, jneg, hE₈, JTriple.mk.injEq]
        refine ⟨?_, ?_, ?_⟩ <;> ext <;>
          simp (disch := omega) only [Function.update_of_ne, Function.update_self, ZOp.eval,
            QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg] <;> simp [show T + 2 + 1 = T + 3 by omega]
      rw [this, v₇, jmul, ite_eq_right (by omega)]
      congr 1
      rw [jmulNat, show (-E k).toNat = (E k).natAbs by omega]
    · rw [f₉ v hvo, hE₈, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        f₇ v hv]
  · obtain ⟨E₉, h₉, v₉, f₉⟩ := copyPt_spec (q := out) (p := T) (by omega) E₇
    refine ⟨E₉, pre (ZBigStep.iteFalse (by simp [ZCond.Holds, hk7, z₇, hneg]) (ZBigStep.skip _)) h₉,
      ?_, fun v hv hvo => ?_⟩
    · rw [v₉, v₇, jmul, ite_eq_left (by omega), jmulNat, show (E k).toNat = (E k).natAbs by omega]
    · rw [f₉ v hvo, f₇ v hv]

end ZInQ.Compiler.IR
