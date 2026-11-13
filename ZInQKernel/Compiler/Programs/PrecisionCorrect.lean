import ZInQKernel.Compiler.Programs.PrecisionIR
import ZInQKernel.Compiler.Programs.PointSpec
import ZInQKernel.Compiler.Programs.CappedSpec
import ZInQKernel.Compiler.Programs.ZLSim
import ZInQKernel.Compiler.Precision.DecisionCorrect

/-!
# Correctness of the precision program

Blueprint: `compiler/natural/programs/precision-ir-correct.md`.

`precisionZ_spec`: from any environment holding the decoded inputs `(n, κ, a, l, j)` in
variables `0, …, 4`, the integer program terminates with outcome `accept` if
`decideInt n κ a l j` and `reject` otherwise. Through the simulation of the integer layer and
the decoding routine, the register program `precisionProgram` is total and accepts `c` iff
`decide5 c = true` iff `accepts c` (`precisionProgram_correct`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace ZInQ.Compiler.IR

open Precision JTriple PrecisionArithmetic PrecisionAlgorithms

theorem guard_reject {c : ZCond} {E : ℕ → ℤ} (h : c.Holds E) :
    ZBigStep (.ite c .reject .skip) E .reject := ZBigStep.iteTrue h (ZBigStep.reject E)

theorem guard_pass {c : ZCond} {E : ℕ → ℤ} (h : ¬ c.Holds E) :
    ZBigStep (.ite c .reject .skip) E (.normal E) := ZBigStep.iteFalse h (ZBigStep.skip E)

theorem guard'_reject {c : ZCond} {E : ℕ → ℤ} (h : ¬ c.Holds E) :
    ZBigStep (.ite c .skip .reject) E .reject := ZBigStep.iteFalse h (ZBigStep.reject E)

theorem guard'_pass {c : ZCond} {E : ℕ → ℤ} (h : c.Holds E) :
    ZBigStep (.ite c .skip .reject) E (.normal E) := ZBigStep.iteTrue h (ZBigStep.skip E)

/-- The expression of `F(n)`. -/
def sixFExpr : IExpr :=
  .mul (.mul (.mul (.mul (.mul (.var 0) (.add (.var 0) (.const 15)))
      (.add (.var 0) (.const 20))) (.add (.var 0) (.const 24))) (.add (.var 0) (.const 30)))
      (.add (.var 0) (.const 60))

theorem earlyCode_eq : earlyCode = (IExpr.code sixFExpr 36 precT ;;;
    .ite (.neq 36 5) .reject .skip ;;; .ite (.neq 1 5) .reject .skip ;;;
    .ite (.lt 2 6) .reject .skip ;;; .ite (.lt 3 6) .reject .skip ;;;
    .assign 37 (.mul 0 2) ;;; .ite (.eq 4 37) .skip .reject) := rfl

theorem earlyCode_spec (E : ℕ → ℤ) (h5 : E 5 = 0) (h6 : E 6 = 1) :
    (¬ EarlyTestsInt (E 0) (E 1) (E 2) (E 3) (E 4) → ZBigStep earlyCode E .reject) ∧
    (EarlyTestsInt (E 0) (E 1) (E 2) (E 3) (E 4) → ∃ E', ZBigStep earlyCode E (.normal E') ∧
      E' 36 = sixF (E 0) ∧ ∀ v < precT, v ≠ 36 → v ≠ 37 → E' v = E v) := by
  obtain ⟨E₁, h₁, v₁, f₁⟩ := IExpr.code_spec sixFExpr 36 precT (by simp [precT])
    (by simp [sixFExpr, IExpr.VarsBelow, precT]) E
  have hF : E₁ 36 = sixF (E 0) := by rw [v₁]; simp [sixFExpr, IExpr.eval, sixF]
  have g : ∀ v, v < 36 → E₁ v = E v := fun v hv => f₁ v (by simp [precT]; omega) (by omega)
  set E₂ := Function.update E₁ 37 (ZOp.eval E₁ (.mul 0 2)) with hE₂
  have g2 : ∀ v, v < 36 → E₂ v = E v := fun v hv => by
    rw [hE₂, Function.update_of_ne (by omega), g v hv]
  have e37 : E₂ 37 = E 0 * E 2 := by simp [hE₂, ZOp.eval, g 0 (by omega), g 2 (by omega)]
  rw [earlyCode_eq]
  constructor
  · intro hn
    simp only [EarlyTestsInt, not_and_or, not_not, not_le] at hn
    by_cases t1 : E₁ 36 = 0
    · exact ZBigStep.seqNormal h₁ (ZBigStep.seqReject (guard_reject (by
        simp [ZCond.Holds, t1, g 5 (by omega), h5])))
    have p1 := guard_pass (c := .neq 36 5) (E := E₁) (by simp [ZCond.Holds, g 5 (by omega), h5]; omega)
    by_cases t2 : E 1 = 0
    · exact ZBigStep.seqNormal h₁ (ZBigStep.seqNormal p1 (ZBigStep.seqReject (guard_reject (by
        simp [ZCond.Holds, g 1 (by omega), t2, g 5 (by omega), h5]))))
    have p2 := guard_pass (c := .neq 1 5) (E := E₁) (by
      simp [ZCond.Holds, g 1 (by omega), g 5 (by omega), h5]; omega)
    by_cases t3 : E 2 < 1
    · exact ZBigStep.seqNormal h₁ (ZBigStep.seqNormal p1 (ZBigStep.seqNormal p2
        (ZBigStep.seqReject (guard_reject (by
          simp [ZCond.Holds, g 2 (by omega), g 6 (by omega), h6]; omega)))))
    have p3 := guard_pass (c := .lt 2 6) (E := E₁) (by
      simp [ZCond.Holds, g 2 (by omega), g 6 (by omega), h6]; omega)
    by_cases t4 : E 3 < 1
    · exact ZBigStep.seqNormal h₁ (ZBigStep.seqNormal p1 (ZBigStep.seqNormal p2
        (ZBigStep.seqNormal p3 (ZBigStep.seqReject (guard_reject (by
          simp [ZCond.Holds, g 3 (by omega), g 6 (by omega), h6]; omega))))))
    have p4 := guard_pass (c := .lt 3 6) (E := E₁) (by
      simp [ZCond.Holds, g 3 (by omega), g 6 (by omega), h6]; omega)
    have t5 : E 4 ≠ E 0 * E 2 := by
      rcases hn with h | h | h | h | h
      · exact absurd ((sixF_eq_zero_iff _).mpr h) (by rw [← hF]; exact t1)
      · exact absurd h t2
      · omega
      · omega
      · exact h
    have c5 : ¬ (ZCond.eq 4 37).Holds E₂ := by
      simp only [ZCond.Holds]; rw [g2 4 (by omega), e37]; exact t5
    exact ZBigStep.seqNormal h₁ (ZBigStep.seqNormal p1 (ZBigStep.seqNormal p2
      (ZBigStep.seqNormal p3 (ZBigStep.seqNormal p4 (ZBigStep.seqNormal (ZBigStep.assign _ _ _)
        (guard'_reject c5))))))
  · rintro ⟨hn, hκ, ha, hl, hj⟩
    have t1 : E₁ 36 ≠ 0 := by rw [hF]; exact fun h => hn ((sixF_eq_zero_iff _).mp h)
    have c1 : ¬ (ZCond.neq 36 5).Holds E₁ := by
      simp only [ZCond.Holds]; rw [g 5 (by omega), h5]; simpa using t1
    have c2 : ¬ (ZCond.neq 1 5).Holds E₁ := by
      simp only [ZCond.Holds]; rw [g 5 (by omega), h5, g 1 (by omega)]; simpa using hκ
    have c3 : ¬ (ZCond.lt 2 6).Holds E₁ := by
      simp only [ZCond.Holds]; rw [g 2 (by omega), g 6 (by omega), h6]; omega
    have c4 : ¬ (ZCond.lt 3 6).Holds E₁ := by
      simp only [ZCond.Holds]; rw [g 3 (by omega), g 6 (by omega), h6]; omega
    have c5 : (ZCond.eq 4 37).Holds E₂ := by
      simp only [ZCond.Holds]; rw [g2 4 (by omega), e37]; exact hj
    refine ⟨E₂, ZBigStep.seqNormal h₁ (ZBigStep.seqNormal (guard_pass c1)
      (ZBigStep.seqNormal (guard_pass c2) (ZBigStep.seqNormal (guard_pass c3)
        (ZBigStep.seqNormal (guard_pass c4) (ZBigStep.seqNormal (ZBigStep.assign _ _ _)
          (guard'_pass c5)))))), ?_, fun v hv h36 h37 => ?_⟩
    · rw [hE₂, Function.update_of_ne (by omega), hF]
    · rw [hE₂, Function.update_of_ne h37, f₁ v hv h36]


/-! ### The three scalar multiplications -/

/-- The body of the loop of `jmul3Code`. -/
def jmul3Body : ZStmt :=
  .ite (.neq 34 5) (.assign 35 (.copy 3)) (.ite (.neq 34 6) (.assign 35 (.copy 2))
      (.assign 35 (.copy 4))) ;;;
    jmulCode 35 28 precT ;;;
    .ite (.neq 34 5) (copyPt 10 28) (.ite (.neq 34 6) (copyPt 16 28) (copyPt 22 28)) ;;;
    .assign 34 (.nadd 34 6)

theorem jmul3Code_eq : jmul3Code = (.assign 34 (.const 0) ;;; .loop 34 7 jmul3Body) := rfl

/-- One iteration: index variable `k`, output slot `q`, counter value `i`. -/
theorem jmul3_iter (E : ℕ → ℤ) (i k q : ℕ) (hik : (i = 0 ∧ k = 3 ∧ q = 10) ∨ (i = 1 ∧ k = 2 ∧ q = 16) ∨
    (i = 2 ∧ k = 4 ∧ q = 22)) (h34 : E 34 = i) (h5 : E 5 = 0) (h6 : E 6 = 1) :
    ∃ E', ZBigStep jmul3Body E (.normal E') ∧ E' 34 = ((i + 1 : ℕ) : ℤ) ∧
      ptOf E' q = jmul (E k) ∧
      ∀ v < precT, (v < 28 ∨ 35 < v) → (v < q ∨ q + 5 < v) → E' v = E v := by
  -- the selection of the index
  obtain ⟨E₁, h₁, v₁, f₁⟩ : ∃ E₁, ZBigStep (.ite (.neq 34 5) (.assign 35 (.copy 3))
      (.ite (.neq 34 6) (.assign 35 (.copy 2)) (.assign 35 (.copy 4)))) E (.normal E₁) ∧
      E₁ 35 = E k ∧ ∀ v, v ≠ 35 → E₁ v = E v := by
    rcases hik with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨_, ZBigStep.iteTrue (by simp [ZCond.Holds, h34, h5]) (ZBigStep.assign _ _ _),
        by simp [ZOp.eval], fun v hv => Function.update_of_ne hv _ _⟩
    · exact ⟨_, ZBigStep.iteFalse (by simp [ZCond.Holds, h34, h5])
        (ZBigStep.iteTrue (by simp [ZCond.Holds, h34, h6]) (ZBigStep.assign _ _ _)),
        by simp [ZOp.eval], fun v hv => Function.update_of_ne hv _ _⟩
    · exact ⟨_, ZBigStep.iteFalse (by simp [ZCond.Holds, h34, h5])
        (ZBigStep.iteFalse (by simp [ZCond.Holds, h34, h6]) (ZBigStep.assign _ _ _)),
        by simp [ZOp.eval], fun v hv => Function.update_of_ne hv _ _⟩
  obtain ⟨E₂, h₂, v₂, f₂⟩ := jmulCode_spec (k := 35) (out := 28) (T := precT)
    (by simp [precT]) (by simp [precT]) E₁
  rw [v₁] at v₂
  have g₂ : ∀ v < precT, (v < 28 ∨ 35 < v) → E₂ v = E v := fun v hv h =>
    by rw [f₂ v hv (by omega), f₁ v (by omega)]
  have e34 : E₂ 34 = i := by rw [f₂ 34 (by simp [precT]) (by omega), f₁ 34 (by omega), h34]
  have e5 : E₂ 5 = 0 := by rw [g₂ 5 (by simp [precT]) (by omega), h5]
  have e6 : E₂ 6 = 1 := by rw [g₂ 6 (by simp [precT]) (by omega), h6]
  -- the store
  obtain ⟨E₃, h₃, v₃, f₃⟩ : ∃ E₃, ZBigStep (.ite (.neq 34 5) (copyPt 10 28)
      (.ite (.neq 34 6) (copyPt 16 28) (copyPt 22 28))) E₂ (.normal E₃) ∧
      ptOf E₃ q = ptOf E₂ 28 ∧ ∀ v, (v < q ∨ q + 5 < v) → E₃ v = E₂ v := by
    rcases hik with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · obtain ⟨E₃, h₃, v₃, f₃⟩ := copyPt_spec (q := 10) (p := 28) (by omega) E₂
      exact ⟨E₃, ZBigStep.iteTrue (by simp [ZCond.Holds, e34, e5]) h₃, v₃, f₃⟩
    · obtain ⟨E₃, h₃, v₃, f₃⟩ := copyPt_spec (q := 16) (p := 28) (by omega) E₂
      exact ⟨E₃, ZBigStep.iteFalse (by simp [ZCond.Holds, e34, e5])
        (ZBigStep.iteTrue (by simp [ZCond.Holds, e34, e6]) h₃), v₃, f₃⟩
    · obtain ⟨E₃, h₃, v₃, f₃⟩ := copyPt_spec (q := 22) (p := 28) (by omega) E₂
      exact ⟨E₃, ZBigStep.iteFalse (by simp [ZCond.Holds, e34, e5])
        (ZBigStep.iteFalse (by simp [ZCond.Holds, e34, e6]) h₃), v₃, f₃⟩
  have hq : q + 5 < 28 := by omega
  refine ⟨_, ZBigStep.seqNormal h₁ (ZBigStep.seqNormal h₂ (ZBigStep.seqNormal h₃
    (ZBigStep.assign _ _ _))), ?_, ?_, fun v hv h1 h2 => ?_⟩
  · simp [ZOp.eval, f₃ 34 (by omega), e34, f₃ 6 (by omega), e6]
  · rw [← v₂, ← v₃]
    exact ptOf_congr fun j hj => Function.update_of_ne (by omega) _ _
  · rw [Function.update_of_ne (by omega), f₃ v h2, g₂ v hv h1]

theorem jmul3Code_spec (E : ℕ → ℤ) (h5 : E 5 = 0) (h6 : E 6 = 1) (h7 : E 7 = 3) :
    ∃ E', ZBigStep jmul3Code E (.normal E') ∧ ptOf E' 10 = jmul (E 3) ∧
      ptOf E' 16 = jmul (E 2) ∧ ptOf E' 22 = jmul (E 4) ∧
      ∀ v < precT, (v < 10 ∨ 35 < v) → E' v = E v := by
  set E₀ := Function.update E 34 (ZOp.eval E (.const 0)) with hE₀
  have g₀ : ∀ v, v ≠ 34 → E₀ v = E v := fun v hv => Function.update_of_ne hv _ _
  obtain ⟨E₁, h₁, c₁, p₁, f₁⟩ := jmul3_iter E₀ 0 3 10 (Or.inl ⟨rfl, rfl, rfl⟩)
    (by simp [hE₀, ZOp.eval]) (by rw [g₀ 5 (by omega), h5]) (by rw [g₀ 6 (by omega), h6])
  have g₁ : ∀ v, v < precT → (v < 10 ∨ (15 < v ∧ v < 28) ∨ 35 < v) → E₁ v = E v :=
    fun v hv' hv => by rw [f₁ v hv' (by omega) (by omega), g₀ v (by omega)]
  obtain ⟨E₂, h₂, c₂, p₂, f₂⟩ := jmul3_iter E₁ 1 2 16 (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
    (by rw [c₁]) (by rw [g₁ 5 (by simp [precT]) (by omega), h5])
    (by rw [g₁ 6 (by simp [precT]) (by omega), h6])
  have g₂ : ∀ v, v < precT → (v < 10 ∨ (21 < v ∧ v < 28) ∨ 35 < v) → E₂ v = E v :=
    fun v hv' hv => by rw [f₂ v hv' (by omega) (by omega), g₁ v hv' (by omega)]
  obtain ⟨E₃, h₃, c₃, p₃, f₃⟩ := jmul3_iter E₂ 2 4 22 (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
    (by rw [c₂]) (by rw [g₂ 5 (by simp [precT]) (by omega), h5])
    (by rw [g₂ 6 (by simp [precT]) (by omega), h6])
  have g₃ : ∀ v, v < precT → (v < 10 ∨ 35 < v) → E₃ v = E v := fun v hv' hv => by
    rw [f₃ v hv' (by omega) (by omega), g₂ v hv' (by omega)]
  have e7 : ∀ E' : ℕ → ℤ, E' 7 = 3 → (E' 7).natAbs = 3 := fun E' h => by rw [h]; rfl
  refine ⟨E₃, ZBigStep.seqNormal (ZBigStep.assign _ _ _)
    (ZBigStep.loopNormal (by simp [ZCond.Holds, hE₀, ZOp.eval, g₀ 7 (by omega), h7])
      h₁ (ZBigStep.loopNormal (by rw [c₁, g₁ 7 (by simp [precT]) (by omega), h7]; decide) h₂
        (ZBigStep.loopNormal (by rw [c₂, g₂ 7 (by simp [precT]) (by omega), h7]; decide) h₃
          (ZBigStep.loopFalse (by rw [c₃, g₃ 7 (by simp [precT]) (by omega), h7]; decide))))),
    ?_, ?_, ?_, g₃⟩
  · rw [ptOf_congr (fun j hj => by rw [f₃ _ (by simp [precT]; omega) (by omega) (by omega),
      f₂ _ (by simp [precT]; omega) (by omega) (by omega)]), p₁, g₀ 3 (by omega)]
  · rw [ptOf_congr (fun j hj => f₃ _ (by simp [precT]; omega) (by omega) (by omega)), p₂,
      g₁ 2 (by simp [precT]) (by omega)]
  · rw [p₃, g₂ 4 (by simp [precT]) (by omega)]


/-! ### Guards and straight-line integer and field assignments -/

/-- A sequence of nonzero guards on pairs, temporaries at `T`, then `c`. -/
def guardsCode (T : ℕ) : List ℕ → ZStmt → ZStmt
  | [], c => c
  | w :: ws, c => guardNonzero w T ;;; guardsCode T ws c

theorem guardsCode_reject {T : ℕ} : ∀ (ws : List ℕ) (c : ZStmt) (E : ℕ → ℤ),
    (∀ w ∈ ws, w + 1 < T) → (∃ w ∈ ws, zsOf E w = 0) → ZBigStep (guardsCode T ws c) E .reject
  | [], _, _, _, ⟨w, hw, _⟩ => absurd hw (by simp)
  | w :: ws, c, E, hws, hex => by
    have hw := hws w (by simp)
    obtain ⟨g1, g2⟩ := guardNonzero_spec hw E
    by_cases h0 : zsOf E w = 0
    · exact ZBigStep.seqReject (g1 h0)
    · obtain ⟨E₁, h₁, f₁⟩ := g2 h0
      refine ZBigStep.seqNormal h₁ (guardsCode_reject ws c E₁
        (fun w' hw' => hws w' (List.mem_cons_of_mem _ hw')) ?_)
      obtain ⟨w', hw', hz⟩ := hex
      rcases List.mem_cons.mp hw' with rfl | hw''
      · exact absurd hz h0
      · refine ⟨w', hw'', ?_⟩
        have := hws w' hw'
        rw [zsOf_congr (f₁ w' (by omega) (by omega)) (f₁ (w' + 1) (by omega) (by omega))]
        exact hz

theorem guardsCode_pass {T : ℕ} : ∀ (ws : List ℕ) (c : ZStmt) (E : ℕ → ℤ),
    (∀ w ∈ ws, w + 1 < T) → (∀ w ∈ ws, zsOf E w ≠ 0) →
    ∃ E', (∀ v < T, E' v = E v) ∧ ∀ o, ZBigStep c E' o → ZBigStep (guardsCode T ws c) E o
  | [], _, E, _, _ => ⟨E, fun _ _ => rfl, fun _ h => h⟩
  | w :: ws, c, E, hws, hnz => by
    have hw := hws w (by simp)
    obtain ⟨E₁, h₁, f₁⟩ := (guardNonzero_spec hw E).2 (hnz w (by simp))
    obtain ⟨E₂, a₂, c₂⟩ := guardsCode_pass ws c E₁
      (fun w' hw' => hws w' (List.mem_cons_of_mem _ hw')) (fun w' hw' => by
        have := hws w' (List.mem_cons_of_mem _ hw')
        rw [zsOf_congr (f₁ w' (by omega) (by omega)) (f₁ (w' + 1) (by omega) (by omega))]
        exact hnz w' (List.mem_cons_of_mem _ hw'))
    exact ⟨E₂, fun v hv => by rw [a₂ v hv, f₁ v (by omega) (by omega)],
      fun o h => ZBigStep.seqNormal h₁ (c₂ o h)⟩

/-- Straight-line integer (`i`) and pair (`f`) assignments. -/
inductive SLStep
  | i (d : ℕ) (e : IExpr)
  | f (d : ℕ) (e : FExpr)

/-- The routine of one step, temporaries from `T`. -/
def SLStep.code (T : ℕ) : SLStep → ZStmt
  | .i d e => IExpr.code e d T
  | .f d e => FExpr.assign d e T

/-- The semantics of one step. -/
def SLStep.sem : SLStep → (ℕ → ℤ) → (ℕ → ℤ)
  | .i d e, E => Function.update E d (e.eval E)
  | .f d e, E => fstep E d e

/-- Destinations and operands below `T`. -/
def SLStep.WF (T : ℕ) : SLStep → Prop
  | .i d e => d < T ∧ e.VarsBelow T
  | .f d e => d + 1 < T ∧ e.VarsBelow T

/-- Straight-line steps followed by `c`. -/
def SLProg.code (T : ℕ) : List SLStep → ZStmt → ZStmt
  | [], c => c
  | st :: l, c => st.code T ;;; SLProg.code T l c

/-- The semantics of straight-line steps. -/
def SLProg.sem : List SLStep → (ℕ → ℤ) → (ℕ → ℤ)
  | [], E => E
  | st :: l, E => SLProg.sem l (st.sem E)

theorem SLStep.sem_congr {T : ℕ} {st : SLStep} (h : st.WF T) {E₁ E₂ : ℕ → ℤ}
    (hE : ∀ v < T, E₁ v = E₂ v) : ∀ v < T, st.sem E₁ v = st.sem E₂ v := by
  intro v hv
  cases st with
  | i d e =>
    have hev : e.eval E₁ = e.eval E₂ := IExpr.eval_congr (fun v hv => hE v hv) h.2
    simp only [SLStep.sem, Function.update_apply, hev]
    split_ifs <;> simp [hE v hv]
  | f d e =>
    have hev : e.eval E₁ = e.eval E₂ := FExpr.eval_congr (fun v hv => hE v hv) h.2
    simp only [SLStep.sem, fstep, Function.update_apply, hev]
    split_ifs <;> simp [hE v hv]

theorem SLProg.sem_congr {T : ℕ} : ∀ {l : List SLStep}, (∀ st ∈ l, st.WF T) →
    ∀ {E₁ E₂ : ℕ → ℤ}, (∀ v < T, E₁ v = E₂ v) → ∀ v < T, SLProg.sem l E₁ v = SLProg.sem l E₂ v
  | [], _, _, _, h => h
  | st :: l, hl, E₁, E₂, h => SLProg.sem_congr (fun s hs => hl s (List.mem_cons_of_mem _ hs))
      (SLStep.sem_congr (hl st (by simp)) h)

theorem SLStep.code_spec {T : ℕ} {st : SLStep} (h : st.WF T) (E : ℕ → ℤ) :
    ∃ E', ZBigStep (st.code T) E (.normal E') ∧ ∀ v < T, E' v = st.sem E v := by
  cases st with
  | i d e =>
    obtain ⟨E', h', v', f'⟩ := IExpr.code_spec e d T h.1 h.2 E
    refine ⟨E', h', fun v hv => ?_⟩
    simp only [SLStep.sem, Function.update_apply]
    split_ifs with hd
    · subst hd; exact v'
    · exact f' v hv hd
  | f d e =>
    obtain ⟨E', h', v', f'⟩ := FExpr.assign_spec h.1 h.2 E
    refine ⟨E', h', fun v hv => ?_⟩
    have hre : E' d = (e.eval E).re := by rw [← v']; rfl
    have him : E' (d + 1) = (e.eval E).im := by rw [← v']; rfl
    simp only [SLStep.sem, fstep, Function.update_apply]
    split_ifs with h1 h2
    · subst h1; exact him
    · subst h2; exact hre
    · exact f' v hv h2 h1

theorem SLProg.code_spec (T : ℕ) : ∀ (l : List SLStep), (∀ st ∈ l, st.WF T) → ∀ E : ℕ → ℤ,
    ∃ E', (∀ v < T, E' v = SLProg.sem l E v) ∧
      ∀ c o, ZBigStep c E' o → ZBigStep (SLProg.code T l c) E o
  | [], _, E => ⟨E, fun _ _ => rfl, fun _ _ h => h⟩
  | st :: l, hl, E => by
    have hl' : ∀ s ∈ l, s.WF T := fun s hs => hl s (List.mem_cons_of_mem _ hs)
    obtain ⟨E₁, h₁, v₁⟩ := SLStep.code_spec (hl st (by simp)) E
    obtain ⟨E₂, a₂, c₂⟩ := SLProg.code_spec T l hl' E₁
    exact ⟨E₂, fun v hv => by rw [a₂ v hv]; exact SLProg.sem_congr hl' v₁ v hv,
      fun c o h => ZBigStep.seqNormal h₁ (c₂ c o h)⟩


/-! ### The tests -/

/-- `ν = -(X Z Ȳ)` of the triple at `p`. -/
def nuF (p : ℕ) : FExpr := .neg (.mul (.mul (.var p) (.var (p + 4))) (.conj (.var (p + 2))))

/-- The straight-line part of the tests: `ν_l, ν_a, ν_j, N_l, N_a, N_j, N(ν_a), U, V, δ, θ`,
and the two sides of the closeness test. -/
def testSL : List SLStep :=
  [.f 40 (nuF 10), .f 42 (nuF 16), .f 44 (nuF 22),
   .i 46 (normI 12), .i 47 (normI 18), .i 48 (normI 24), .i 49 (normI 42),
   .i 50 (.add (.abs (.var 40)) (.abs (.var 41))), .i 51 (.abs (.var 46)),
   .i 52 (.mul (.var 48) (.var 49)),
   .f 54 (.mul (.mul (.var 44) (.conj (.var 42))) (.int 47)),
   .i 56 (.mul (.abs (.sub (.var 54) (.mul (.var 0) (.var 52)))) (.var 51)),
   .i 57 (.mul (.var 50) (.abs (.var 52)))]

/-- The tail of the tests after the closeness inequality. -/
def testRest : ZStmt :=
  .ite (.lt 56 57) .skip .reject ;;;
  .assign 58 (.nsub 51 6) ;;; .assign 59 (.nmul 8 50) ;;; .assign 60 (.div 58 59) ;;;
  .ite (.neq 60 5) .reject .skip ;;;
  IExpr.code (.abs (.mul (.var 1) (.var 36))) 61 precT ;;;
  cBoundCode 60 62 61 precT ;;;
  .assign 63 (.copy 60) ;;; divFourCode 63 62 precT ;;;
  .ite (.nlt 5 63) .accept .reject

theorem testCode_eq : testCode = guardsCode precT [14, 20, 26, 12, 18, 24]
    (SLProg.code precT testSL testRest) := rfl

theorem fstep_self (E : ℕ → ℤ) (d : ℕ) (e : FExpr) : fstep E d e d = (e.eval E).re := by
  simp [fstep]

theorem fstep_succ (E : ℕ → ℤ) (d : ℕ) (e : FExpr) : fstep E d e (d + 1) = (e.eval E).im := by
  simp [fstep]

theorem fstep_ne (E : ℕ → ℤ) {d v : ℕ} (e : FExpr) (h1 : v ≠ d) (h2 : v ≠ d + 1) :
    fstep E d e v = E v := by
  simp [fstep, h1, h2]

theorem zsOf_update_ne (E : ℕ → ℤ) {d w : ℕ} (v : ℤ) (h1 : w ≠ d) (h2 : w + 1 ≠ d) :
    zsOf (Function.update E d v) w = zsOf E w := by
  simp [zsOf, Function.update_of_ne h1, Function.update_of_ne h2]

theorem zs_intCast (z : ℤ) : (⟨z, 0⟩ : Zs) = (z : Zs) := by ext <;> simp

theorem normJ_eq (Y : Zs) : QuadraticAlgebra.norm Y = Y.re * Y.re - 2 * (Y.im * Y.im) := by
  rw [QuadraticAlgebra.norm_def]; ring

/-- Evaluating the straight-line part. -/
macro "sl_simp" : tactic => `(tactic| simp (disch := omega) only [testSL, SLProg.sem, SLStep.sem,
    IExpr.eval, FExpr.eval, normI, nuF, Function.update_self, Function.update_of_ne, fstep_self,
    fstep_succ, fstep_ne, zsOf_fstep_self, zsOf_fstep_ne, zsOf_update_ne])


theorem testSL_frame (E : ℕ → ℤ) : ∀ v < 40, SLProg.sem testSL E v = E v := by
  intro v hv; sl_simp

set_option maxHeartbeats 2000000 in
theorem testSL_values (E : ℕ → ℤ) :
    SLProg.sem testSL E 50 = |(nuJ (ptOf E 10)).re| + |(nuJ (ptOf E 10)).im| ∧
    SLProg.sem testSL E 51 = |normJ (ptOf E 10)| ∧
    SLProg.sem testSL E 52 = ratioDen (ptOf E 16) (ptOf E 22) ∧
    SLProg.sem testSL E 56 = |ratioNum (ptOf E 16) (ptOf E 22) - E 0 * ratioDen (ptOf E 16)
      (ptOf E 22)| * |normJ (ptOf E 10)| ∧
    SLProg.sem testSL E 57 = (|(nuJ (ptOf E 10)).re| + |(nuJ (ptOf E 10)).im|) *
      |ratioDen (ptOf E 16) (ptOf E 22)| := by
  have hN : ∀ p, normJ (ptOf E p) = E (p + 2) * E (p + 2) - 2 * (E (p + 2 + 1) * E (p + 2 + 1)) :=
    fun p => by simp only [normJ, ptOf, normJ_eq, zsOf]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · sl_simp; rfl
  · sl_simp; rw [hN]
  · sl_simp; simp only [ratioDen, hN, normJ_eq]; rfl
  · sl_simp; simp only [ratioDen, ratioNum, hN, normJ_eq, zs_intCast]; rfl
  · sl_simp; simp only [ratioDen, hN, normJ_eq]; rfl


theorem testRest_spec (E : ℕ → ℤ) {U V : ℕ} {κ F lhs rhs : ℤ} (h5 : E 5 = 0) (h6 : E 6 = 1)
    (h8 : E 8 = 4) (h1 : E 1 = κ) (h36 : E 36 = F) (h50 : E 50 = U) (h51 : E 51 = V)
    (h56 : E 56 = lhs) (h57 : E 57 = rhs) :
    ZBigStep testRest E (if (if lhs < rhs then (if (V - 1) / (4 * U) = 0 then false else
      decide (1 ≤ divFourLoop ((V - 1) / (4 * U)) (cappedBound ((V - 1) / (4 * U))
        (κ * F).natAbs))) else false) then .accept else .reject) := by
  by_cases hc : lhs < rhs
  swap
  · rw [ite_eq_right hc]
    exact ZBigStep.seqReject (guard'_reject (by simp [ZCond.Holds, h56, h57, hc]))
  rw [ite_eq_left hc]
  have p1 := guard'_pass (c := .lt 56 57) (E := E) (by simp [ZCond.Holds, h56, h57, hc])
  set L := (V - 1) / (4 * U) with hL
  -- `L`
  set E₃ := Function.update (Function.update (Function.update E 58 (ZOp.eval E (.nsub 51 6))) 59
    (ZOp.eval (Function.update E 58 (ZOp.eval E (.nsub 51 6))) (.nmul 8 50))) 60
    (ZOp.eval (Function.update (Function.update E 58 (ZOp.eval E (.nsub 51 6))) 59
    (ZOp.eval (Function.update E 58 (ZOp.eval E (.nsub 51 6))) (.nmul 8 50))) (.div 58 59)) with hE₃
  have g₃ : ∀ v, v < 58 → E₃ v = E v := fun v hv => by
    rw [hE₃, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  have e60 : E₃ 60 = (L : ℤ) := by
    simp [hE₃, ZOp.eval, h51, h6, h8, h50, hL]
  have pre : ∀ {o}, ZBigStep (.ite (.neq 60 5) .reject .skip ;;;
      IExpr.code (.abs (.mul (.var 1) (.var 36))) 61 precT ;;; cBoundCode 60 62 61 precT ;;;
      .assign 63 (.copy 60) ;;; divFourCode 63 62 precT ;;; .ite (.nlt 5 63) .accept .reject) E₃ o →
      ZBigStep testRest E o := fun h =>
    ZBigStep.seqNormal p1 (ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.seqNormal
      (ZBigStep.assign _ _ _) (ZBigStep.seqNormal (ZBigStep.assign _ _ _) h)))
  by_cases hL0 : L = 0
  · rw [ite_eq_left hL0]
    exact pre (ZBigStep.seqReject (guard_reject (by
      simp [ZCond.Holds, e60, g₃ 5 (by omega), h5, hL0])))
  rw [ite_eq_right hL0]
  have p2 := guard_pass (c := .neq 60 5) (E := E₃) (by
    simp [ZCond.Holds, e60, g₃ 5 (by omega), h5]; omega)
  -- `M`
  obtain ⟨E₄, h₄, v₄, f₄⟩ := IExpr.code_spec (.abs (.mul (.var 1) (.var 36))) 61 precT
    (by simp [precT]) (by simp [IExpr.VarsBelow, precT]) E₃
  have g₄ : ∀ v, v < precT → v ≠ 61 → E₄ v = E₃ v := f₄
  have e61 : (E₄ 61).natAbs = (κ * F).natAbs := by
    rw [v₄]; simp [IExpr.eval, g₃ 1 (by omega), g₃ 36 (by omega), h1, h36, Int.natAbs_mul,
      Int.natAbs_abs]
  -- `β`
  obtain ⟨E₅, h₅, v₅, f₅⟩ := cBoundCode_spec (Lv := 60) (d := 62) (M := 61) (V := precT)
    (by simp [precT]) (by simp [precT]) (by simp [precT]) (E := E₄)
    (by rw [g₄ 60 (by simp [precT]) (by omega), e60, Int.natAbs_natCast]) e61
  -- the division loop
  set E₆ := Function.update E₅ 63 (ZOp.eval E₅ (.copy 60)) with hE₆
  have e63 : E₆ 63 = (L : ℤ) := by
    simp [hE₆, ZOp.eval, f₅ 60 (by simp [precT]) (by omega), g₄ 60 (by simp [precT]) (by omega),
      e60]
  obtain ⟨E₇, h₇, v₇, f₇⟩ := divFourCode_spec (x := 63) (β := 62) (T := precT) (by simp [precT])
    (by simp [precT]) (by omega) (E := E₆) e63
    (by rw [hE₆, Function.update_of_ne (by omega), v₅, Int.natAbs_natCast])
  have e5 : E₇ 5 = 0 := by
    rw [f₇ 5 (by simp [precT]) (by omega), hE₆, Function.update_of_ne (by omega),
      f₅ 5 (by simp [precT]) (by omega), g₄ 5 (by simp [precT]) (by omega), g₃ 5 (by omega), h5]
  have tail : ∀ o, ZBigStep (.ite (.nlt 5 63) .accept .reject) E₇ o →
      ZBigStep testRest E o := fun o h => pre (ZBigStep.seqNormal p2 (ZBigStep.seqNormal h₄
        (ZBigStep.seqNormal h₅ (ZBigStep.seqNormal (ZBigStep.assign _ _ _)
          (ZBigStep.seqNormal h₇ h)))))
  by_cases hfin : 1 ≤ divFourLoop L (cappedBound L (κ * F).natAbs)
  · rw [decide_eq_true hfin]
    exact tail _ (ZBigStep.iteTrue (by simp [ZCond.Holds, e5, v₇]; omega) (ZBigStep.accept _))
  · rw [decide_eq_false hfin]
    exact tail _ (ZBigStep.iteFalse (by simp [ZCond.Holds, e5, v₇]; omega) (ZBigStep.reject _))


theorem testCode_spec (E : ℕ → ℤ) (h5 : E 5 = 0) (h6 : E 6 = 1) (h8 : E 8 = 4)
    (h36 : E 36 = sixF (E 0)) (hl : ptOf E 10 = jmul (E 3)) (ha : ptOf E 16 = jmul (E 2))
    (hj : ptOf E 22 = jmul (E 4)) (hE : EarlyTestsInt (E 0) (E 1) (E 2) (E 3) (E 4)) :
    ZBigStep testCode E (if decideInt (E 0) (E 1) (E 2) (E 3) (E 4) then .accept else .reject) := by
  rw [testCode_eq]
  simp only [decideInt, ite_eq_left hE, ← hl, ← ha, ← hj]
  have hws : ∀ w ∈ [14, 20, 26, 12, 18, 24], w + 1 < precT := by simp [precT]
  by_cases hz : (ptOf E 10).Z = 0 ∨ (ptOf E 16).Z = 0 ∨ (ptOf E 22).Z = 0 ∨
      (ptOf E 10).Y = 0 ∨ (ptOf E 16).Y = 0 ∨ (ptOf E 22).Y = 0
  · rw [ite_eq_left hz]
    refine guardsCode_reject _ _ E hws ?_
    simp only [ptOf] at hz
    rcases hz with h | h | h | h | h | h
    · exact ⟨14, by simp, h⟩
    · exact ⟨20, by simp, h⟩
    · exact ⟨26, by simp, h⟩
    · exact ⟨12, by simp, h⟩
    · exact ⟨18, by simp, h⟩
    · exact ⟨24, by simp, h⟩
  rw [ite_eq_right hz]
  simp only [ptOf, not_or] at hz
  obtain ⟨z1, z2, z3, z4, z5, z6⟩ := hz
  obtain ⟨E₁, a₁, c₁⟩ := guardsCode_pass [14, 20, 26, 12, 18, 24] (SLProg.code precT testSL testRest)
    E hws (by simp only [List.mem_cons, List.mem_nil_iff, or_false]; rintro w (rfl | rfl | rfl |
      rfl | rfl | rfl) <;> assumption)
  have hwf : ∀ st ∈ testSL, st.WF precT := by
    intro st hst
    simp only [testSL, List.mem_cons, List.mem_nil_iff, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [SLStep.WF, FExpr.VarsBelow, IExpr.VarsBelow, nuF, normI, precT]
  obtain ⟨E₂, a₂, c₂⟩ := SLProg.code_spec precT testSL hwf E₁
  have hP : ∀ p, p + 5 < precT → ptOf E₁ p = ptOf E p :=
    fun p hp => ptOf_congr fun i hi => a₁ _ (by omega)
  obtain ⟨v50, v51, v52, v56, v57⟩ := testSL_values E₁
  have e10 := hP 10 (by simp [precT]); have e16 := hP 16 (by simp [precT])
  have e22 := hP 22 (by simp [precT])
  simp only [e10, e16, e22] at v50 v51 v52 v56 v57
  have fr : ∀ v < 40, E₂ v = E v := fun v hv => by
    rw [a₂ v (by simp [precT]; omega), testSL_frame E₁ v hv, a₁ v (by simp [precT]; omega)]
  have hU : E₂ 50 = (epsU (ptOf E 10) : ℤ) := by
    rw [a₂ 50 (by simp [precT]), v50, epsU]; push_cast; simp [Int.natCast_natAbs]
  have hV : E₂ 51 = (epsV (ptOf E 10) : ℤ) := by
    rw [a₂ 51 (by simp [precT]), v51, epsV, Int.natCast_natAbs]
  have h56 : E₂ 56 = |ratioNum (ptOf E 16) (ptOf E 22) - E 0 * ratioDen (ptOf E 16) (ptOf E 22)| *
      (epsV (ptOf E 10) : ℤ) := by
    rw [a₂ 56 (by simp [precT]), v56, epsV, Int.natCast_natAbs, ← fr 0 (by omega),
      a₂ 0 (by simp [precT]), testSL_frame E₁ 0 (by omega)]
  have h57 : E₂ 57 = (epsU (ptOf E 10) : ℤ) * |ratioDen (ptOf E 16) (ptOf E 22)| := by
    rw [a₂ 57 (by simp [precT]), v57, epsU]; push_cast; simp [Int.natCast_natAbs]
  have := testRest_spec E₂ (U := epsU (ptOf E 10)) (V := epsV (ptOf E 10)) (κ := E 1)
    (F := sixF (E 0)) (by rw [fr 5 (by omega), h5]) (by rw [fr 6 (by omega), h6])
    (by rw [fr 8 (by omega), h8]) (fr 1 (by omega)) (by rw [a₂ 36 (by simp [precT]),
      testSL_frame E₁ 36 (by omega), a₁ 36 (by simp [precT]), h36]) hU hV h56 h57
  exact c₁ _ (c₂ _ _ this)


/-! ### The whole program -/

theorem precisionZ_spec (E : ℕ → ℤ) :
    ZBigStep precisionZ E (if decideInt (E 0) (E 1) (E 2) (E 3) (E 4) then .accept else .reject) := by
  set E₀ := Function.update (Function.update (Function.update (Function.update E 5
    (ZOp.eval E (.const 0))) 6 (ZOp.eval (Function.update E 5 (ZOp.eval E (.const 0))) (.const 1)))
    7 (ZOp.eval (Function.update (Function.update E 5 (ZOp.eval E (.const 0))) 6
    (ZOp.eval (Function.update E 5 (ZOp.eval E (.const 0))) (.const 1))) (.const 3))) 8
    (ZOp.eval (Function.update (Function.update (Function.update E 5 (ZOp.eval E (.const 0))) 6
    (ZOp.eval (Function.update E 5 (ZOp.eval E (.const 0))) (.const 1))) 7
    (ZOp.eval (Function.update (Function.update E 5 (ZOp.eval E (.const 0))) 6
    (ZOp.eval (Function.update E 5 (ZOp.eval E (.const 0))) (.const 1))) (.const 3))) (.const 4))
    with hE₀
  have g₀ : ∀ v < 5, E₀ v = E v := fun v hv => by
    rw [hE₀, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have e5 : E₀ 5 = 0 := by simp [hE₀, ZOp.eval]
  have e6 : E₀ 6 = 1 := by simp [hE₀, ZOp.eval]
  have e7 : E₀ 7 = 3 := by simp [hE₀, ZOp.eval]
  have e8 : E₀ 8 = 4 := by simp [hE₀, ZOp.eval]
  have pre : ∀ {o}, ZBigStep (earlyCode ;;; jmul3Code ;;; testCode) E₀ o →
      ZBigStep precisionZ E o := fun h =>
    ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.seqNormal (ZBigStep.assign _ _ _)
      (ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.seqNormal (ZBigStep.assign _ _ _) h)))
  rw [← g₀ 0 (by omega), ← g₀ 1 (by omega), ← g₀ 2 (by omega), ← g₀ 3 (by omega),
    ← g₀ 4 (by omega)]
  obtain ⟨er, ep⟩ := earlyCode_spec E₀ e5 e6
  by_cases hE : EarlyTestsInt (E₀ 0) (E₀ 1) (E₀ 2) (E₀ 3) (E₀ 4)
  · obtain ⟨E₁, h₁, v₁, f₁⟩ := ep hE
    have g₁ : ∀ v < 36, E₁ v = E₀ v := fun v hv => f₁ v (by simp [precT]; omega) (by omega) (by omega)
    obtain ⟨E₂, h₂, p₁, p₂, p₃, f₂⟩ := jmul3Code_spec E₁ (by rw [g₁ 5 (by omega), e5])
      (by rw [g₁ 6 (by omega), e6]) (by rw [g₁ 7 (by omega), e7])
    have g₂ : ∀ v < 10, E₂ v = E₀ v := fun v hv => by
      rw [f₂ v (by simp [precT]; omega) (by omega), g₁ v (by omega)]
    have := testCode_spec E₂ (by rw [g₂ 5 (by omega), e5]) (by rw [g₂ 6 (by omega), e6])
      (by rw [g₂ 8 (by omega), e8])
      (by rw [f₂ 36 (by simp [precT]) (by omega), v₁, g₂ 0 (by omega)])
      (by rw [p₁, g₁ 3 (by omega), g₂ 3 (by omega)])
      (by rw [p₂, g₁ 2 (by omega), g₂ 2 (by omega)])
      (by rw [p₃, g₁ 4 (by omega), g₂ 4 (by omega)])
      (by rw [g₂ 0 (by omega), g₂ 1 (by omega), g₂ 2 (by omega), g₂ 3 (by omega),
        g₂ 4 (by omega)]; exact hE)
    rw [g₂ 0 (by omega), g₂ 1 (by omega), g₂ 2 (by omega), g₂ 3 (by omega),
        g₂ 4 (by omega)] at this
    exact pre (ZBigStep.seqNormal h₁ (ZBigStep.seqNormal h₂ this))
  · have hd : decideInt (E₀ 0) (E₀ 1) (E₀ 2) (E₀ 3) (E₀ 4) = false := by
      simp only [decideInt, ite_eq_right hE]
    rw [hd]
    exact pre (ZBigStep.seqReject (er hE))


/-! ### Variable and register bounds -/

/-- One more than the largest variable of a right-hand side. -/
def ZOp.varsBound : ZOp → ℕ
  | .const _ => 0
  | .copy a | .neg a | .abs a => a + 1
  | .add a b | .sub a b | .mul a b | .div a b | .mod a b | .nadd a b | .nsub a b | .nmul a b =>
    max a b + 1

/-- One more than the largest variable of a test. -/
def ZCond.varsBound : ZCond → ℕ
  | .lt a b | .eq a b | .nlt a b | .neq a b => max a b + 1

/-- One more than the largest variable of a statement. -/
def ZStmt.varsBound : ZStmt → ℕ
  | .assign k o => max (k + 1) o.varsBound
  | .seq s u => max s.varsBound u.varsBound
  | .ite c s u => max c.varsBound (max s.varsBound u.varsBound)
  | .loop a b s => max (max a b + 1) s.varsBound
  | .skip | .accept | .reject => 0

theorem ZStmt.varsBelow_of_varsBound {K : ℕ} : ∀ {S : ZStmt}, S.varsBound ≤ K → S.VarsBelow K
  | .assign k o, h => by
    simp only [ZStmt.varsBound, max_le_iff] at h
    refine ⟨by omega, ?_⟩
    cases o <;> simp only [ZOp.varsBound] at h <;> simp only [ZOp.VarsBelow] <;> omega
  | .seq s u, h => by
    simp only [ZStmt.varsBound, max_le_iff] at h
    exact ⟨varsBelow_of_varsBound h.1, varsBelow_of_varsBound h.2⟩
  | .ite c s u, h => by
    simp only [ZStmt.varsBound, max_le_iff] at h
    refine ⟨?_, varsBelow_of_varsBound h.2.1, varsBelow_of_varsBound h.2.2⟩
    cases c <;> simp only [ZCond.varsBound] at h <;> simp only [ZCond.VarsBelow] <;> omega
  | .loop a b s, h => by
    simp only [ZStmt.varsBound, max_le_iff] at h
    exact ⟨by omega, by omega, varsBelow_of_varsBound h.2⟩
  | .skip, _ => trivial
  | .accept, _ => trivial
  | .reject, _ => trivial

/-- One more than the largest register of a right-hand side. -/
def Op.regsBound : Op → ℕ
  | .const _ => 0
  | .copy y => y + 1
  | .add y z | .sub y z | .mul y z | .div y z | .mod y z => max y z + 1

/-- One more than the largest register of a statement. -/
def Stmt.regsBound : Stmt → ℕ
  | .assign x o => max (x + 1) o.regsBound
  | .seq s t => max s.regsBound t.regsBound
  | .ifLt y z s t | .ifEq y z s t => max (max y z + 1) (max s.regsBound t.regsBound)
  | .whileLt y z s => max (max y z + 1) s.regsBound
  | .accept | .reject => 0

theorem Stmt.regsBelow_of_regsBound {b : ℕ} : ∀ {S : Stmt}, S.regsBound ≤ b → S.RegsBelow b
  | .assign x o, h => by
    simp only [Stmt.regsBound, max_le_iff] at h
    refine ⟨by omega, ?_⟩
    cases o <;> simp only [Op.regsBound] at h <;> simp only [Op.RegsBelow] <;> omega
  | .seq s t, h => by
    simp only [Stmt.regsBound, max_le_iff] at h
    exact ⟨regsBelow_of_regsBound h.1, regsBelow_of_regsBound h.2⟩
  | .ifLt y z s t, h => by
    simp only [Stmt.regsBound, max_le_iff] at h
    exact ⟨by omega, by omega, regsBelow_of_regsBound h.2.1, regsBelow_of_regsBound h.2.2⟩
  | .ifEq y z s t, h => by
    simp only [Stmt.regsBound, max_le_iff] at h
    exact ⟨by omega, by omega, regsBelow_of_regsBound h.2.1, regsBelow_of_regsBound h.2.2⟩
  | .whileLt y z s, h => by
    simp only [Stmt.regsBound, max_le_iff] at h
    exact ⟨by omega, by omega, regsBelow_of_regsBound h.2⟩
  | .accept, _ => trivial
  | .reject, _ => trivial

theorem precisionZ_varsBound : precisionZ.varsBound ≤ precisionVars := by decide +kernel


theorem precisionProgram_regsBound :
    precisionProgram.body.regsBound ≤ precisionProgram.bound := by decide +kernel

theorem precisionProgram_wf : precisionProgram.WF :=
  ⟨Stmt.regsBelow_of_regsBound precisionProgram_regsBound, by decide +kernel⟩

/-! ### Correctness -/

theorem ReprInt.frame {ρ ρ' : ℕ → ℕ} {x : SInt} {z : ℤ} (h : ReprInt ρ x z)
    (h1 : ρ' x.sign = ρ x.sign) (h2 : ρ' x.mag = ρ x.mag) : ReprInt ρ' x z :=
  ⟨by rw [h1]; exact h.1, by rw [h2]; exact h.2⟩

theorem zvar_prec (k : ℕ) : zvar precOff k = ⟨5 + 2 * k, 5 + 2 * k + 1⟩ := rfl

/-- After the decoding, the variable pairs represent `(dec c₀, …, dec c₄, 0, 0, …)`. -/
theorem decodeInputs_spec (c : Fin 5 → ℕ) : ∃ ρ, BigStep (decodeInputs precRegT)
    (RM.initFile c) (.normal ρ) ∧ ReprEnv precOff precisionVars ρ
      (fun k => if h : k < 5 then dec (c ⟨k, h⟩) else 0) := by
  have hT : precRegT = 805 := rfl
  have hb : ∀ k, k < 5 → (zvar precOff k).Below precRegT := fun k hk =>
    ⟨by rw [zvar_prec, hT]; simp only; omega, by rw [zvar_prec, hT]; simp only; omega⟩
  obtain ⟨ρ₁, h₁, r₁, f₁⟩ := sDecode_spec (c := 0) (hb 0 (by omega)) (by rw [hT]; omega) (zvar_ne _ _)
    (RM.initFile c)
  obtain ⟨ρ₂, h₂, r₂, f₂⟩ := sDecode_spec (c := 1) (hb 1 (by omega)) (by rw [hT]; omega) (zvar_ne _ _) ρ₁
  obtain ⟨ρ₃, h₃, r₃, f₃⟩ := sDecode_spec (c := 2) (hb 2 (by omega)) (by rw [hT]; omega) (zvar_ne _ _) ρ₂
  obtain ⟨ρ₄, h₄, r₄, f₄⟩ := sDecode_spec (c := 3) (hb 3 (by omega)) (by rw [hT]; omega) (zvar_ne _ _) ρ₃
  obtain ⟨ρ₅, h₅, r₅, f₅⟩ := sDecode_spec (c := 4) (hb 4 (by omega)) (by rw [hT]; omega) (zvar_ne _ _) ρ₄
  simp only [zvar_prec, hT] at f₁ f₂ f₃ f₄ f₅ r₁ r₂ r₃ r₄ r₅
  -- the inputs are read before being overwritten (registers below `5` are never written)
  have i1 : ρ₁ 1 = c 1 := by rw [f₁ 1 (by omega) (by omega) (by omega)]; rfl
  have i2 : ρ₂ 2 = c 2 := by
    rw [f₂ 2 (by omega) (by omega) (by omega), f₁ 2 (by omega) (by omega) (by omega)]; rfl
  have i3 : ρ₃ 3 = c 3 := by
    rw [f₃ 3 (by omega) (by omega) (by omega), f₂ 3 (by omega) (by omega) (by omega),
      f₁ 3 (by omega) (by omega) (by omega)]; rfl
  have i4 : ρ₄ 4 = c 4 := by
    rw [f₄ 4 (by omega) (by omega) (by omega), f₃ 4 (by omega) (by omega) (by omega),
      f₂ 4 (by omega) (by omega) (by omega), f₁ 4 (by omega) (by omega) (by omega)]; rfl
  have i0 : RM.initFile c 0 = c 0 := rfl
  rw [i0] at r₁; rw [i1] at r₂; rw [i2] at r₃; rw [i3] at r₄; rw [i4] at r₅
  refine ⟨ρ₅, BigStep.seqNormal h₁ (BigStep.seqNormal h₂ (BigStep.seqNormal h₃
    (BigStep.seqNormal h₄ h₅))), fun k hk => ?_⟩
  rw [zvar_prec]
  by_cases h5 : k < 5
  · simp only [h5, dite_true]
    interval_cases k
    · exact r₁.frame (by simp only; rw [f₅ _ (by omega) (by omega) (by omega),
        f₄ _ (by omega) (by omega) (by omega), f₃ _ (by omega) (by omega) (by omega),
        f₂ _ (by omega) (by omega) (by omega)]) (by simp only; rw [f₅ _ (by omega) (by omega) (by omega),
        f₄ _ (by omega) (by omega) (by omega), f₃ _ (by omega) (by omega) (by omega),
        f₂ _ (by omega) (by omega) (by omega)])
    · exact r₂.frame (by simp only; rw [f₅ _ (by omega) (by omega) (by omega),
        f₄ _ (by omega) (by omega) (by omega), f₃ _ (by omega) (by omega) (by omega)])
        (by simp only; rw [f₅ _ (by omega) (by omega) (by omega),
        f₄ _ (by omega) (by omega) (by omega), f₃ _ (by omega) (by omega) (by omega)])
    · exact r₃.frame (by simp only; rw [f₅ _ (by omega) (by omega) (by omega),
        f₄ _ (by omega) (by omega) (by omega)]) (by simp only; rw [f₅ _ (by omega) (by omega) (by omega),
        f₄ _ (by omega) (by omega) (by omega)])
    · exact r₄.frame (by simp only; rw [f₅ _ (by omega) (by omega) (by omega)])
        (by simp only; rw [f₅ _ (by omega) (by omega) (by omega)])
    · exact r₅
  · simp only [h5, dite_false]
    have hk' : k < 400 := hk
    have F : ∀ i, i < 805 → 15 ≤ i → ρ₅ i = 0 := fun i hi h => by
      rw [f₅ i hi (by omega) (by omega), f₄ i hi (by omega) (by omega), f₃ i hi (by omega) (by omega),
        f₂ i hi (by omega) (by omega), f₁ i hi (by omega) (by omega), RM.initFile_of_le c (by omega)]
    refine ⟨?_, ?_⟩
    · show ρ₅ (5 + 2 * k) = _; rw [F _ (by omega) (by omega)]; rfl
    · show ρ₅ (5 + 2 * k + 1) = _; rw [F _ (by omega) (by omega)]; rfl


/-- The outcome of the precision program on `c`: `accept` if `decide5 c`, else `reject`. -/
theorem precisionProgram_bigStep (c : Fin 5 → ℕ) :
    BigStep precisionProgram.body (RM.initFile c) (if decide5 c then .accept else .reject) := by
  obtain ⟨ρ, h, r⟩ := decodeInputs_spec c
  set E : ℕ → ℤ := fun k => if h : k < 5 then dec (c ⟨k, h⟩) else 0 with hE
  have hz := precisionZ_spec E
  have hd : decideInt (E 0) (E 1) (E 2) (E 3) (E 4) = decide5 c := rfl
  rw [hd] at hz
  have hsim := ZStmt.compile_sim hz (ZStmt.varsBelow_of_varsBound precisionZ_varsBound) precRegT
    (le_refl _) ρ r
  by_cases hc : decide5 c = true
  · rw [ite_eq_left hc] at hsim ⊢
    exact BigStep.seqNormal h hsim
  · rw [ite_eq_right hc] at hsim ⊢
    exact BigStep.seqNormal h hsim

/-- **The precision program is total.** -/
theorem precisionProgram_total : precisionProgram.Total := fun c =>
  ⟨_, precisionProgram_bigStep c⟩

/-- **Correctness of the precision program**: it accepts `c` iff `decide(c) = true`. -/
theorem precisionProgram_correct (c : Fin 5 → ℕ) :
    precisionProgram.Accepts c ↔ decide5 c = true := by
  have h := precisionProgram_bigStep c
  constructor
  · intro ha
    by_contra hc
    rw [ite_eq_right hc] at h
    exact Outcome.noConfusion (ha.deterministic h)
  · intro hc
    rw [ite_eq_left hc] at h
    exact h

/-- The precision program accepts `c` iff `accepts(c)`. -/
theorem precisionProgram_accepts_iff (c : Fin 5 → ℕ) :
    precisionProgram.Accepts c ↔ accepts c :=
  (precisionProgram_correct c).trans (decide5_iff c)

/-- On an input failing an early test the outcome is `reject`. -/
theorem precisionProgram_reject_of_not_early (c : Fin 5 → ℕ) (h : ¬ EarlyTests c) :
    BigStep precisionProgram.body (RM.initFile c) .reject := by
  have hb := precisionProgram_bigStep c
  have hd : decide5 c = false := by
    simp only [decide5, decideInt]; rw [ite_eq_right (show ¬ EarlyTestsInt _ _ _ _ _ from h)]
  rwa [hd, ite_eq_right (by simp)] at hb

end ZInQ.Compiler.IR
