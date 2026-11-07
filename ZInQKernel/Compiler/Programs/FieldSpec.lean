import ZInQKernel.Compiler.Programs.Field

/-!
# Integer and quadratic-field routines (specifications)

Blueprint: `compiler/natural/programs/ir-field-routines.md`.

Specifications over integer environments: constants (`natConst_spec`, `intConst_spec`),
integer expressions (`IExpr.code_spec`), `ℤ[s]`-expressions (`FExpr.code_spec`,
`FExpr.assign_spec`), multiplication in `ℤ[s]` (`fMul_spec`), the zero flag and the nonzero
guard. Every routine writes only its result variables and the temporaries from its base `T`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace ZInQ.Compiler.IR

open Precision

/-- Plain integer statements: assignments, `skip`, sequencing and conditionals. -/
def ZStmt.Plain : ZStmt → Prop
  | .assign _ _ | .skip => True
  | .seq s t | .ite _ s t => s.Plain ∧ t.Plain
  | _ => False

/-- A Boolean comparison of integers (no instance arguments, so `simp` can rewrite inside). -/
def zblt (x y : ℤ) : Bool := Nat.blt 0 (y - x).toNat

theorem zblt_iff (x y : ℤ) : zblt x y = true ↔ x < y := by
  simp only [zblt, Nat.blt_eq]; omega

/-- A Boolean equality of integers. -/
def zbeq (x y : ℤ) : Bool := Nat.beq (x - y).natAbs 0

theorem zbeq_iff (x y : ℤ) : zbeq x y = true ↔ x = y := by
  simp only [zbeq, Nat.beq_eq]; omega

/-- The Boolean value of a test. -/
def ZCond.btest (E : ℕ → ℤ) : ZCond → Bool
  | .lt a b => zblt (E a) (E b)
  | .eq a b => zbeq (E a) (E b)
  | .nlt a b => Nat.blt (E a).natAbs (E b).natAbs
  | .neq a b => Nat.beq (E a).natAbs (E b).natAbs

theorem ZCond.btest_iff (E : ℕ → ℤ) (c : ZCond) : c.btest E = true ↔ c.Holds E := by
  cases c <;> simp [ZCond.btest, ZCond.Holds, zblt_iff, zbeq_iff, Nat.blt_eq, Nat.beq_eq]

/-- The environment computed by a plain integer statement. -/
def ZStmt.execZ : ZStmt → (ℕ → ℤ) → (ℕ → ℤ)
  | .assign k o, E => Function.update E k (o.eval E)
  | .seq s t, E => t.execZ (s.execZ E)
  | .ite c s t, E => cond (c.btest E) (s.execZ E) (t.execZ E)
  | _, E => E

theorem zbigStep_execZ : ∀ {S : ZStmt}, S.Plain → ∀ E, ZBigStep S E (.normal (S.execZ E))
  | .assign k o, _, E => ZBigStep.assign k o E
  | .skip, _, E => ZBigStep.skip E
  | .seq s t, h, E => ZBigStep.seqNormal (zbigStep_execZ h.1 E) (zbigStep_execZ h.2 _)
  | .ite c s t, h, E => by
    by_cases hc : c.Holds E
    · have hb := (c.btest_iff E).mpr hc
      simp only [ZStmt.execZ, hb, Bool.cond_true]; exact ZBigStep.iteTrue hc (zbigStep_execZ h.1 E)
    · have hb : c.btest E = false := by
        cases h' : c.btest E
        · rfl
        · exact absurd ((c.btest_iff E).mp h') hc
      simp only [ZStmt.execZ, hb, Bool.cond_false]; exact ZBigStep.iteFalse hc (zbigStep_execZ h.2 E)

theorem zcond_apply {α β : Type*} (b : Bool) (f g : α → β) (a : α) :
    (cond b f g) a = cond b (f a) (g a) := by cases b <;> rfl

/-- The simp set evaluating plain integer statements on symbolic variables. -/
macro "zexec_simp" : tactic => `(tactic| simp (disch := omega) only [ZStmt.execZ, ZOp.eval,
    ZCond.btest, Function.update_self, Function.update_of_ne, ite_apply, zcond_apply])

/-- Turn the Boolean tests into propositions after the evaluation. -/
macro "zcond_simp" : tactic => `(tactic| simp only [Bool.cond_eq_ite, Nat.blt_eq, Nat.beq_eq,
    zblt_iff, zbeq_iff] at *)

/-! ### Constants -/

theorem natConstF_spec : ∀ (f k n T : ℕ), k ≠ T → ∀ E : ℕ → ℤ, ∃ E',
    ZBigStep (natConstF f k n T) E (.normal E') ∧ E' k = n ∧ ∀ v, v ≠ k → v ≠ T → E' v = E v
  | 0, k, n, T, _, E => ⟨_, ZBigStep.assign _ _ _, by simp [ZOp.eval],
      fun v h1 _ => Function.update_of_ne h1 _ _⟩
  | f + 1, k, n, T, hkT, E => by
    by_cases hn : n < 64
    · simp only [natConstF, hn, ite_true]
      exact ⟨_, ZBigStep.assign _ _ _, by simp [ZOp.eval], fun v h1 _ => Function.update_of_ne h1 _ _⟩
    · simp only [natConstF, hn, ite_false]
      obtain ⟨E₁, h₁, v₁, f₁⟩ := natConstF_spec f k (n / 64) T hkT E
      refine ⟨_, ZBigStep.seqNormal h₁ (zbigStep_execZ (by simp [ZStmt.Plain]) _), ?_, ?_⟩
      · zexec_simp; rw [v₁, show Int.natAbs 64 = 64 from rfl]; omega
      · intro v h1 h2; zexec_simp; exact f₁ v h1 h2

theorem natConst_spec (k n T : ℕ) (hkT : k ≠ T) (E : ℕ → ℤ) : ∃ E',
    ZBigStep (natConst k n T) E (.normal E') ∧ E' k = n ∧ ∀ v, v ≠ k → v ≠ T → E' v = E v :=
  natConstF_spec 12 k n T hkT E

theorem intConst_spec (k : ℕ) (c : ℤ) (T : ℕ) (hkT : k ≠ T) (E : ℕ → ℤ) : ∃ E',
    ZBigStep (intConst k c T) E (.normal E') ∧ E' k = c ∧ ∀ v, v ≠ k → v ≠ T → E' v = E v := by
  obtain ⟨E₁, h₁, v₁, f₁⟩ := natConst_spec k c.natAbs T hkT E
  by_cases hc : c < 0
  · simp only [intConst, hc, ite_true]
    refine ⟨_, ZBigStep.seqNormal h₁ (ZBigStep.assign _ _ _), ?_, ?_⟩
    · simp only [ZOp.eval, Function.update_self, v₁]; omega
    · intro v h1 h2; rw [Function.update_of_ne h1]; exact f₁ v h1 h2
  · simp only [intConst, hc, ite_false]
    exact ⟨E₁, h₁, by rw [v₁]; omega, f₁⟩


/-! ### Integer expressions -/

/-- All variables of an integer expression are below `T`. -/
def IExpr.VarsBelow (T : ℕ) : IExpr → Prop
  | .var w => w < T
  | .const _ => True
  | .add e f | .sub e f | .mul e f => e.VarsBelow T ∧ f.VarsBelow T
  | .neg e | .abs e => e.VarsBelow T

theorem IExpr.VarsBelow.mono {T T' : ℕ} (h : T ≤ T') {e : IExpr} (he : e.VarsBelow T) :
    e.VarsBelow T' := by
  induction e with
  | var w => exact lt_of_lt_of_le he h
  | const _ => trivial
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | mul _ _ ih1 ih2 => exact ⟨ih1 he.1, ih2 he.2⟩
  | neg _ ih | abs _ ih => exact ih he

theorem IExpr.eval_congr {T : ℕ} {E E' : ℕ → ℤ} (hE : ∀ v < T, E' v = E v) {e : IExpr}
    (he : e.VarsBelow T) : e.eval E' = e.eval E := by
  induction e with
  | var w => exact hE w he
  | const _ => rfl
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | mul _ _ ih1 ih2 =>
    simp only [IExpr.eval, ih1 he.1, ih2 he.2]
  | neg _ ih | abs _ ih => simp only [IExpr.eval, ih he]

/-- The contract of `e.code d T`. -/
def IExpr.CodeSpec (e : IExpr) : Prop :=
  ∀ d T, d < T → e.VarsBelow T → ∀ E : ℕ → ℤ, ∃ E', ZBigStep (e.code d T) E (.normal E') ∧
    E' d = e.eval E ∧ ∀ v < T, v ≠ d → E' v = E v

theorem IExpr.arg_spec {e : IExpr} (he : e.CodeSpec) {s tt : ℕ} (hs : s < tt)
    (hv : e.VarsBelow s) (E : ℕ → ℤ) : ∃ E', ZBigStep (IExpr.arg e (e.code s tt)) E (.normal E') ∧
      E' (e.loc s) = e.eval E ∧ ∀ v < tt, v ≠ s → E' v = E v := by
  cases e with
  | var w => exact ⟨E, ZBigStep.skip E, rfl, fun _ _ _ => rfl⟩
  | _ => exact he s tt hs (hv.mono (by omega)) E

theorem IExpr.loc_lt {e : IExpr} {s : ℕ} (hv : e.VarsBelow s) : e.loc s ≤ s := by
  cases e with
  | var w => exact le_of_lt hv
  | _ => exact le_rfl

theorem IExpr.code_spec : ∀ e : IExpr, e.CodeSpec
  | .var w => fun d T hd hv E => ⟨_, ZBigStep.assign _ _ _, by simp [ZOp.eval, IExpr.eval],
      fun v _ hv => Function.update_of_ne hv _ _⟩
  | .const c => fun d T hd hv E => by
    obtain ⟨E', h, v, f⟩ := intConst_spec d c T (by omega) E
    exact ⟨E', h, v, fun w hw h1 => f w h1 (by omega)⟩
  | .neg e => fun d T hd hv E => by
    obtain ⟨E₁, h₁, v₁, f₁⟩ := IExpr.arg_spec (code_spec e) (s := T) (tt := T + 2) (by omega) hv E
    refine ⟨_, ZBigStep.seqNormal h₁ (ZBigStep.assign _ _ _), ?_, fun w hw h1 => ?_⟩
    · simp [ZOp.eval, IExpr.eval, v₁]
    · rw [Function.update_of_ne h1, f₁ w (by omega) (by omega)]
  | .abs e => fun d T hd hv E => by
    obtain ⟨E₁, h₁, v₁, f₁⟩ := IExpr.arg_spec (code_spec e) (s := T) (tt := T + 2) (by omega) hv E
    refine ⟨_, ZBigStep.seqNormal h₁ (ZBigStep.assign _ _ _), ?_, fun w hw h1 => ?_⟩
    · simp [ZOp.eval, IExpr.eval, v₁]
    · rw [Function.update_of_ne h1, f₁ w (by omega) (by omega)]
  | .add e f => fun d T hd hv E => by
    obtain ⟨E₁, h₁, v₁, f₁⟩ := IExpr.arg_spec (code_spec e) (s := T) (tt := T + 2) (by omega) hv.1 E
    obtain ⟨E₂, h₂, v₂, f₂⟩ := IExpr.arg_spec (code_spec f) (s := T + 1) (tt := T + 2) (by omega)
      (hv.2.mono (by omega)) E₁
    have l1 := IExpr.loc_lt hv.1
    have e1 : E₂ (e.loc T) = e.eval E := by rw [f₂ _ (by omega) (by omega), v₁]
    have e2 : E₂ (f.loc (T + 1)) = f.eval E := by
      rw [v₂, IExpr.eval_congr (fun v hv => f₁ v (by omega) (by omega)) hv.2]
    refine ⟨_, ZBigStep.seqNormal h₁ (ZBigStep.seqNormal h₂ (ZBigStep.assign _ _ _)), ?_,
      fun w hw h1 => ?_⟩
    · simp [ZOp.eval, IExpr.eval, e1, e2]
    · rw [Function.update_of_ne h1, f₂ w (by omega) (by omega), f₁ w (by omega) (by omega)]
  | .sub e f => fun d T hd hv E => by
    obtain ⟨E₁, h₁, v₁, f₁⟩ := IExpr.arg_spec (code_spec e) (s := T) (tt := T + 2) (by omega) hv.1 E
    obtain ⟨E₂, h₂, v₂, f₂⟩ := IExpr.arg_spec (code_spec f) (s := T + 1) (tt := T + 2) (by omega)
      (hv.2.mono (by omega)) E₁
    have l1 := IExpr.loc_lt hv.1
    have e1 : E₂ (e.loc T) = e.eval E := by rw [f₂ _ (by omega) (by omega), v₁]
    have e2 : E₂ (f.loc (T + 1)) = f.eval E := by
      rw [v₂, IExpr.eval_congr (fun v hv => f₁ v (by omega) (by omega)) hv.2]
    refine ⟨_, ZBigStep.seqNormal h₁ (ZBigStep.seqNormal h₂ (ZBigStep.assign _ _ _)), ?_,
      fun w hw h1 => ?_⟩
    · simp [ZOp.eval, IExpr.eval, e1, e2]
    · rw [Function.update_of_ne h1, f₂ w (by omega) (by omega), f₁ w (by omega) (by omega)]
  | .mul e f => fun d T hd hv E => by
    obtain ⟨E₁, h₁, v₁, f₁⟩ := IExpr.arg_spec (code_spec e) (s := T) (tt := T + 2) (by omega) hv.1 E
    obtain ⟨E₂, h₂, v₂, f₂⟩ := IExpr.arg_spec (code_spec f) (s := T + 1) (tt := T + 2) (by omega)
      (hv.2.mono (by omega)) E₁
    have l1 := IExpr.loc_lt hv.1
    have e1 : E₂ (e.loc T) = e.eval E := by rw [f₂ _ (by omega) (by omega), v₁]
    have e2 : E₂ (f.loc (T + 1)) = f.eval E := by
      rw [v₂, IExpr.eval_congr (fun v hv => f₁ v (by omega) (by omega)) hv.2]
    refine ⟨_, ZBigStep.seqNormal h₁ (ZBigStep.seqNormal h₂ (ZBigStep.assign _ _ _)), ?_,
      fun w hw h1 => ?_⟩
    · simp [ZOp.eval, IExpr.eval, e1, e2]
    · rw [Function.update_of_ne h1, f₂ w (by omega) (by omega), f₁ w (by omega) (by omega)]


/-! ### Quadratic-field expressions -/

/-- All variables of an `ℤ[s]`-expression lie below `T` (a pair `w` needs `w + 1 < T`). -/
def FExpr.VarsBelow (T : ℕ) : FExpr → Prop
  | .var w => w + 1 < T
  | .int w => w < T
  | .const _ _ => True
  | .add e f | .sub e f | .mul e f => e.VarsBelow T ∧ f.VarsBelow T
  | .neg e | .conj e => e.VarsBelow T

theorem FExpr.VarsBelow.mono {T T' : ℕ} (h : T ≤ T') {e : FExpr} (he : e.VarsBelow T) :
    e.VarsBelow T' := by
  induction e with
  | var w => exact lt_of_lt_of_le he h
  | int w => exact lt_of_lt_of_le he h
  | const _ _ => trivial
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | mul _ _ ih1 ih2 => exact ⟨ih1 he.1, ih2 he.2⟩
  | neg _ ih | conj _ ih => exact ih he

theorem FExpr.eval_congr {T : ℕ} {E E' : ℕ → ℤ} (hE : ∀ v < T, E' v = E v) {e : FExpr}
    (he : e.VarsBelow T) : e.eval E' = e.eval E := by
  induction e with
  | var w => simp only [FExpr.eval, zsOf, hE w (by simp only [FExpr.VarsBelow] at he; omega),
      hE (w + 1) he]
  | int w => simp only [FExpr.eval, hE w he]
  | const _ _ => rfl
  | add _ _ ih1 ih2 | sub _ _ ih1 ih2 | mul _ _ ih1 ih2 =>
    simp only [FExpr.eval, ih1 he.1, ih2 he.2]
  | neg _ ih | conj _ ih => simp only [FExpr.eval, ih he]

theorem fMul_spec {d a b T : ℕ} (hda : a + 1 < d ∨ d + 2 ≤ a) (hdb : b + 1 < d ∨ d + 2 ≤ b)
    (hTa : a + 1 < T) (hTb : b + 1 < T) (hTd : d + 1 < T) (E : ℕ → ℤ) : ∃ E',
    ZBigStep (fMul d a b T) E (.normal E') ∧ zsOf E' d = zsOf E a * zsOf E b ∧
      ∀ v, v ≠ d → v ≠ d + 1 → v ≠ T → E' v = E v := by
  refine ⟨_, zbigStep_execZ (by simp [fMul, ZStmt.Plain]) E, ?_, fun v h1 h2 h3 => ?_⟩
  · simp only [fMul, zsOf]; zexec_simp
    ext <;> simp <;> ring
  · simp only [fMul]; zexec_simp

/-- The contract of `e.code d T`. -/
def FExpr.CodeSpec (e : FExpr) : Prop :=
  ∀ d T, d + 2 ≤ T → e.VarsBelow d → ∀ E : ℕ → ℤ, ∃ E', ZBigStep (e.code d T) E (.normal E') ∧
    zsOf E' d = e.eval E ∧ ∀ v < T, v ≠ d → v ≠ d + 1 → E' v = E v

theorem FExpr.arg_spec {e : FExpr} (he : e.CodeSpec) {s tt : ℕ} (hs : s + 2 ≤ tt)
    (hv : e.VarsBelow s) (E : ℕ → ℤ) : ∃ E', ZBigStep (FExpr.arg e (e.code s tt)) E (.normal E') ∧
      zsOf E' (e.loc s) = e.eval E ∧ ∀ v < tt, v ≠ s → v ≠ s + 1 → E' v = E v := by
  cases e with
  | var w => exact ⟨E, ZBigStep.skip E, rfl, fun _ _ _ _ => rfl⟩
  | _ => exact he s tt hs hv E

theorem FExpr.loc_cases {e : FExpr} {T : ℕ} (hv : e.VarsBelow T) :
    e.loc T = T ∨ e.loc T + 1 < T := by
  cases e with
  | var w => exact Or.inr hv
  | _ => exact Or.inl rfl

theorem FExpr.loc_cases' {e : FExpr} {d T : ℕ} (hv : e.VarsBelow d) (h : d ≤ T) :
    e.loc T = T ∨ e.loc T + 1 < d := by
  cases e with
  | var w => exact Or.inr hv
  | _ => exact Or.inl rfl

theorem FExpr.code_spec : ∀ e : FExpr, e.CodeSpec
  | .var w => fun d T hd hv E => by
    refine ⟨_, zbigStep_execZ (by simp [FExpr.code, ZStmt.Plain]) E, ?_, fun v hv h1 h2 => ?_⟩
    · simp only [FExpr.code, FExpr.eval, zsOf]; try simp only [FExpr.VarsBelow] at hv
      zexec_simp
    · simp only [FExpr.code]; zexec_simp
  | .int w => fun d T hd hv E => by
    refine ⟨_, zbigStep_execZ (by simp [FExpr.code, ZStmt.Plain]) E, ?_, fun v hv h1 h2 => ?_⟩
    · simp only [FExpr.code, FExpr.eval, zsOf]; try simp only [FExpr.VarsBelow] at hv
      zexec_simp
    · simp only [FExpr.code]; zexec_simp
  | .const a b => fun d T hd hv E => by
    obtain ⟨E₁, h₁, v₁, f₁⟩ := intConst_spec d a T (by omega) E
    obtain ⟨E₂, h₂, v₂, f₂⟩ := intConst_spec (d + 1) b T (by omega) E₁
    refine ⟨E₂, ZBigStep.seqNormal h₁ h₂, ?_, fun v hv h1 h2 => ?_⟩
    · simp only [zsOf, FExpr.eval, v₂, f₂ d (by omega) (by omega), v₁]
    · rw [f₂ v h2 (by omega), f₁ v h1 (by omega)]
  | .add e f => fun d T hd hv E => by
    obtain ⟨E₁, h₁, v₁, f₁⟩ := FExpr.arg_spec (code_spec e) (s := T) (tt := T + 4) (by omega)
      (hv.1.mono (by omega)) E
    obtain ⟨E₂, h₂, v₂, f₂⟩ := FExpr.arg_spec (code_spec f) (s := T + 2) (tt := T + 4) (by omega)
      (hv.2.mono (by omega)) E₁
    have l1 := FExpr.loc_cases' hv.1 (T := T) (by omega)
    have l2 := FExpr.loc_cases' hv.2 (T := T + 2) (by omega)
    have e1 : zsOf E₂ (e.loc T) = e.eval E := by
      rw [← v₁]; simp only [zsOf]; rw [f₂ _ (by omega) (by omega) (by omega),
        f₂ _ (by omega) (by omega) (by omega)]
    have e2 : zsOf E₂ (f.loc (T + 2)) = f.eval E := by
      rw [v₂, FExpr.eval_congr (fun v hv => f₁ v (by omega) (by omega) (by omega)) hv.2]
    refine ⟨_, ZBigStep.seqNormal h₁ (ZBigStep.seqNormal h₂ (zbigStep_execZ (by simp [ZStmt.Plain]) _)),
      ?_, fun w hw h1 h2 => ?_⟩
    · rw [FExpr.eval, ← e1, ← e2]; simp only [zsOf]; zexec_simp
      ext <;> simp
    · zexec_simp; rw [f₂ w (by omega) (by omega) (by omega), f₁ w (by omega) (by omega) (by omega)]
  | .sub e f => fun d T hd hv E => by
    obtain ⟨E₁, h₁, v₁, f₁⟩ := FExpr.arg_spec (code_spec e) (s := T) (tt := T + 4) (by omega)
      (hv.1.mono (by omega)) E
    obtain ⟨E₂, h₂, v₂, f₂⟩ := FExpr.arg_spec (code_spec f) (s := T + 2) (tt := T + 4) (by omega)
      (hv.2.mono (by omega)) E₁
    have l1 := FExpr.loc_cases' hv.1 (T := T) (by omega)
    have l2 := FExpr.loc_cases' hv.2 (T := T + 2) (by omega)
    have e1 : zsOf E₂ (e.loc T) = e.eval E := by
      rw [← v₁]; simp only [zsOf]; rw [f₂ _ (by omega) (by omega) (by omega),
        f₂ _ (by omega) (by omega) (by omega)]
    have e2 : zsOf E₂ (f.loc (T + 2)) = f.eval E := by
      rw [v₂, FExpr.eval_congr (fun v hv => f₁ v (by omega) (by omega) (by omega)) hv.2]
    refine ⟨_, ZBigStep.seqNormal h₁ (ZBigStep.seqNormal h₂ (zbigStep_execZ (by simp [ZStmt.Plain]) _)),
      ?_, fun w hw h1 h2 => ?_⟩
    · rw [FExpr.eval, ← e1, ← e2]; simp only [zsOf]; zexec_simp
      ext <;> simp
    · zexec_simp; rw [f₂ w (by omega) (by omega) (by omega), f₁ w (by omega) (by omega) (by omega)]
  | .mul e f => fun d T hd hv E => by
    obtain ⟨E₁, h₁, v₁, f₁⟩ := FExpr.arg_spec (code_spec e) (s := T) (tt := T + 4) (by omega)
      (hv.1.mono (by omega)) E
    obtain ⟨E₂, h₂, v₂, f₂⟩ := FExpr.arg_spec (code_spec f) (s := T + 2) (tt := T + 4) (by omega)
      (hv.2.mono (by omega)) E₁
    have l1 := FExpr.loc_cases' hv.1 (T := T) (by omega)
    have l2 := FExpr.loc_cases' hv.2 (T := T + 2) (by omega)
    have e1 : zsOf E₂ (e.loc T) = e.eval E := by
      rw [← v₁]; simp only [zsOf]; rw [f₂ _ (by omega) (by omega) (by omega),
        f₂ _ (by omega) (by omega) (by omega)]
    have e2 : zsOf E₂ (f.loc (T + 2)) = f.eval E := by
      rw [v₂, FExpr.eval_congr (fun v hv => f₁ v (by omega) (by omega) (by omega)) hv.2]
    obtain ⟨E₃, h₃, v₃, f₃⟩ := fMul_spec (d := d) (a := e.loc T) (b := f.loc (T + 2)) (T := T + 4)
      (by omega) (by omega) (by omega) (by omega) (by omega) E₂
    refine ⟨E₃, ZBigStep.seqNormal h₁ (ZBigStep.seqNormal h₂ h₃), ?_, fun w hw h1 h2 => ?_⟩
    · rw [v₃, e1, e2]; rfl
    · rw [f₃ w h1 h2 (by omega), f₂ w (by omega) (by omega) (by omega),
        f₁ w (by omega) (by omega) (by omega)]
  | .neg e => fun d T hd hv E => by
    obtain ⟨E₁, h₁, v₁, f₁⟩ := FExpr.arg_spec (code_spec e) (s := T) (tt := T + 4) (by omega)
      (hv.mono (by omega)) E
    have l1 := FExpr.loc_cases' (e := e) hv (T := T) (by omega)
    refine ⟨_, ZBigStep.seqNormal h₁ (zbigStep_execZ (by simp [ZStmt.Plain]) _), ?_,
      fun w hw h1 h2 => ?_⟩
    · rw [FExpr.eval, ← v₁]; simp only [zsOf]; zexec_simp
      ext <;> simp
    · zexec_simp; rw [f₁ w (by omega) (by omega) (by omega)]
  | .conj e => fun d T hd hv E => by
    obtain ⟨E₁, h₁, v₁, f₁⟩ := FExpr.arg_spec (code_spec e) (s := T) (tt := T + 4) (by omega)
      (hv.mono (by omega)) E
    have l1 := FExpr.loc_cases' (e := e) hv (T := T) (by omega)
    refine ⟨_, ZBigStep.seqNormal h₁ (zbigStep_execZ (by simp [ZStmt.Plain]) _), ?_,
      fun w hw h1 h2 => ?_⟩
    · rw [FExpr.eval, ← v₁]; simp only [zsOf]; zexec_simp
      ext <;> simp
    · zexec_simp; rw [f₁ w (by omega) (by omega) (by omega)]

theorem FExpr.assign_spec {d T : ℕ} {e : FExpr} (hd : d + 1 < T) (he : e.VarsBelow T)
    (E : ℕ → ℤ) : ∃ E', ZBigStep (FExpr.assign d e T) E (.normal E') ∧
      zsOf E' d = e.eval E ∧ ∀ v < T, v ≠ d → v ≠ d + 1 → E' v = E v := by
  obtain ⟨E₁, h₁, v₁, f₁⟩ := FExpr.code_spec e T (T + 2) (by omega) he E
  refine ⟨_, ZBigStep.seqNormal h₁ (zbigStep_execZ (by simp [ZStmt.Plain]) _), ?_,
    fun v hv h1 h2 => ?_⟩
  · rw [← v₁]; simp only [zsOf]; zexec_simp
  · zexec_simp; exact f₁ v (by omega) (by omega) (by omega)

theorem zsOf_eq_zero_iff (E : ℕ → ℤ) (w : ℕ) : zsOf E w = 0 ↔ E w = 0 ∧ E (w + 1) = 0 := by
  simp [zsOf, QuadraticAlgebra.ext_iff]

theorem zeroFlag_spec {f w T : ℕ} (hfT : f ≠ T) (hfw : f ≠ w ∧ f ≠ w + 1)
    (hTw : T ≠ w ∧ T ≠ w + 1) (E : ℕ → ℤ) : ∃ E', ZBigStep (zeroFlag f w T) E (.normal E') ∧
      E' f = (if zsOf E w = 0 then 1 else 0) ∧ ∀ v, v ≠ f → v ≠ T → E' v = E v := by
  set E₁ := Function.update (Function.update E f 0) T 0 with hE₁
  have e0 : E₁ w = E w := by rw [hE₁, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have e1 : E₁ (w + 1) = E (w + 1) := by
    rw [hE₁, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have eT : E₁ T = 0 := by simp [hE₁]
  have ef : E₁ f = 0 := by rw [hE₁, Function.update_of_ne hfT]; simp
  have fr : ∀ v, v ≠ f → v ≠ T → E₁ v = E v := fun v h1 h2 => by
    rw [hE₁, Function.update_of_ne h2, Function.update_of_ne h1]
  have pre : ∀ {o}, ZBigStep (.ite (.neq w T) (.ite (.neq (w + 1) T) (.assign f (.const 1)) .skip)
      .skip) E₁ o → ZBigStep (zeroFlag f w T) E o := fun h =>
    ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.seqNormal (ZBigStep.assign _ _ _) h)
  simp only [zsOf_eq_zero_iff]
  by_cases h0 : E w = 0
  · by_cases h1 : E (w + 1) = 0
    · refine ⟨_, pre (ZBigStep.iteTrue (by simp [ZCond.Holds, e0, eT, h0])
        (ZBigStep.iteTrue (by simp [ZCond.Holds, e1, eT, h1]) (ZBigStep.assign _ _ _))), ?_, ?_⟩
      · simp [ZOp.eval, h0, h1]
      · intro v hv1 hv2; rw [Function.update_of_ne hv1, fr v hv1 hv2]
    · refine ⟨_, pre (ZBigStep.iteTrue (by simp [ZCond.Holds, e0, eT, h0])
        (ZBigStep.iteFalse (by simp [ZCond.Holds, e1, eT, h1]) (ZBigStep.skip _))), ?_, fr⟩
      simp [ef, h1]
  · refine ⟨_, pre (ZBigStep.iteFalse (by simp [ZCond.Holds, e0, eT, h0]) (ZBigStep.skip _)), ?_, fr⟩
    simp [ef, h0]

theorem guardNonzero_spec {w T : ℕ} (hw : w + 1 < T) (E : ℕ → ℤ) :
    (zsOf E w = 0 → ZBigStep (guardNonzero w T) E .reject) ∧
    (zsOf E w ≠ 0 → ∃ E', ZBigStep (guardNonzero w T) E (.normal E') ∧
      ∀ v, v ≠ T → v ≠ T + 1 → E' v = E v) := by
  obtain ⟨E₁, h₁, v₁, f₁⟩ := zeroFlag_spec (f := T) (w := w) (T := T + 1) (by omega)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ E
  have hz : (Function.update E₁ (T + 1) 0) (T + 1) = 0 := by simp
  have hT : (Function.update E₁ (T + 1) 0) T = E₁ T := Function.update_of_ne (by omega) _ _
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [ite_eq_left h] at v₁
    exact ZBigStep.seqNormal h₁ (ZBigStep.seqNormal (ZBigStep.assign _ _ _)
      (ZBigStep.iteFalse (by simp [ZCond.Holds, ZOp.eval, hT, v₁]) (ZBigStep.reject _)))
  · rw [ite_eq_right h] at v₁
    refine ⟨_, ZBigStep.seqNormal h₁ (ZBigStep.seqNormal (ZBigStep.assign _ _ _)
      (ZBigStep.iteTrue (by simp [ZCond.Holds, ZOp.eval, hT, v₁]) (ZBigStep.skip _))), ?_⟩
    intro v h1 h2
    rw [Function.update_of_ne (by simpa using h2), f₁ v h1 h2]

end ZInQ.Compiler.IR
