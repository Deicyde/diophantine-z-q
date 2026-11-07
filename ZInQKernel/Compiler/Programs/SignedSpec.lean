import ZInQKernel.Compiler.Programs.Signed
import ZInQKernel.Compiler.Precision.Encoding

/-!
# Signed integer routines (specifications)

Blueprint: `compiler/natural/programs/ir-integer-routines.md`.

Each routine of `Signed.lean`, started from a file in which the operand pairs represent
integers `z₁, z₂` (normalized sign and magnitude), terminates normally; the result pair
represents the corresponding integer; every register below the temporary base `t` other than
the result registers is unchanged (the temporaries are the registers from `t` on). Results may
alias operands. The routines are loop free, so their runs are computed by `Stmt.execF`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace ZInQ.Compiler.IR

/-- Plain statements: assignments, sequencing and conditionals. -/
def Stmt.Plain : Stmt → Prop
  | .assign _ _ => True
  | .seq s t | .ifLt _ _ s t | .ifEq _ _ s t => s.Plain ∧ t.Plain
  | _ => False

/-- The file computed by a plain statement. -/
def Stmt.execF : Stmt → (ℕ → ℕ) → (ℕ → ℕ)
  | .assign x o, ρ => Function.update ρ x (o.eval ρ)
  | .seq s t, ρ => t.execF (s.execF ρ)
  | .ifLt y z s t, ρ => if ρ y < ρ z then s.execF ρ else t.execF ρ
  | .ifEq y z s t, ρ => if ρ y = ρ z then s.execF ρ else t.execF ρ
  | _, ρ => ρ

theorem bigStep_execF : ∀ {S : Stmt}, S.Plain → ∀ ρ, BigStep S ρ (.normal (S.execF ρ))
  | .assign x o, _, ρ => BigStep.assign x o ρ
  | .seq s t, h, ρ => BigStep.seqNormal (bigStep_execF h.1 ρ) (bigStep_execF h.2 _)
  | .ifLt y z s t, h, ρ => by
    by_cases hc : ρ y < ρ z
    · simp only [Stmt.execF, hc, ite_true]; exact BigStep.ifLtTrue hc (bigStep_execF h.1 ρ)
    · simp only [Stmt.execF, hc, ite_false]; exact BigStep.ifLtFalse hc (bigStep_execF h.2 ρ)
  | .ifEq y z s t, h, ρ => by
    by_cases hc : ρ y = ρ z
    · simp only [Stmt.execF, hc, ite_true]; exact BigStep.ifEqTrue hc (bigStep_execF h.1 ρ)
    · simp only [Stmt.execF, hc, ite_false]; exact BigStep.ifEqFalse hc (bigStep_execF h.2 ρ)

theorem mul_sub_sub_one (g m : ℕ) : g * (m - (m - 1)) = if m = 0 then 0 else g := by
  rcases m with _ | m <;> simp

/-- A routine's contract: normal termination with `ρ'`, the result pair representing `z`,
and the registers below `t` other than the result unchanged. -/
def SContract (S : Stmt) (o : SInt) (t : ℕ) (ρ : ℕ → ℕ) (z : ℤ) : Prop :=
  ∃ ρ', BigStep S ρ (.normal ρ') ∧ ReprInt ρ' o z ∧
    ∀ i < t, i ≠ o.sign → i ≠ o.mag → ρ' i = ρ i

theorem SContract.of_execF {S : Stmt} {o : SInt} {t : ℕ} {ρ : ℕ → ℕ} {z : ℤ} (hS : S.Plain)
    (h1 : S.execF ρ o.sign = if z < 0 then 1 else 0) (h2 : S.execF ρ o.mag = z.natAbs)
    (h3 : ∀ i < t, i ≠ o.sign → i ≠ o.mag → S.execF ρ i = ρ i) : SContract S o t ρ z :=
  ⟨_, bigStep_execF hS ρ, ⟨h1, h2⟩, h3⟩

/-- The operand registers of the routines lie below the temporary base. -/
structure SInt.Below (x : SInt) (t : ℕ) : Prop where
  sign : x.sign < t
  mag : x.mag < t

theorem sAdd_spec {o x y : SInt} {t : ℕ} (ho : o.Below t) (hx : x.Below t) (hy : y.Below t)
    (hne : o.sign ≠ o.mag) {ρ : ℕ → ℕ} {zx zy : ℤ} (rx : ReprInt ρ x zx) (ry : ReprInt ρ y zy) :
    SContract (sAdd o x y t) o t ρ (zx + zy) := by
  obtain ⟨hos, hom⟩ := ho; obtain ⟨hxs, hxm⟩ := hx; obtain ⟨hys, hym⟩ := hy
  obtain ⟨rxs, rxm⟩ := rx; obtain ⟨rys, rym⟩ := ry
  have rxs' : (ρ x.sign = 1 ∧ zx < 0) ∨ (ρ x.sign = 0 ∧ 0 ≤ zx) := by split_ifs at rxs <;> omega
  have rys' : (ρ y.sign = 1 ∧ zy < 0) ∨ (ρ y.sign = 0 ∧ 0 ≤ zy) := by split_ifs at rys <;> omega
  clear rxs rys
  refine SContract.of_execF (by simp [sAdd, normSign, Stmt.Plain]) ?_ ?_ ?_
  all_goals simp (disch := omega) only [sAdd, normSign, Stmt.execF, Op.eval,
    Function.update_self, Function.update_of_ne, ite_apply, mul_sub_sub_one]
  · split_ifs <;> omega
  · split_ifs <;> omega
  · intro i hi h1 h2
    simp (disch := omega) only [Function.update_of_ne]
    split_ifs <;> simp (disch := omega) only [Function.update_of_ne]


/-- The simp set evaluating a plain routine on symbolic registers. -/
macro "exec_simp" : tactic => `(tactic| simp (disch := omega) only [Stmt.execF, Op.eval,
    Function.update_self, Function.update_of_ne, ite_apply, mul_sub_sub_one])

theorem sDecode_spec {o : SInt} {c t : ℕ} (ho : o.Below t) (hc : c < t) (hne : o.sign ≠ o.mag)
    (ρ : ℕ → ℕ) : SContract (sDecode o c t) o t ρ (Precision.dec (ρ c)) := by
  obtain ⟨hos, hom⟩ := ho
  refine SContract.of_execF (by simp [sDecode, Stmt.Plain]) ?_ ?_ ?_
  all_goals simp only [sDecode]; exec_simp
  · unfold Precision.dec; split_ifs <;> omega
  · unfold Precision.dec; split_ifs <;> omega
  · intro i hi h1 h2; exec_simp

theorem sConst_spec {o : SInt} (c : ℤ) (t : ℕ) (hne : o.sign ≠ o.mag) (ρ : ℕ → ℕ) :
    SContract (sConst o c) o t ρ c := by
  refine SContract.of_execF (by simp [sConst, Stmt.Plain]) ?_ ?_ ?_
  all_goals simp only [sConst]; exec_simp
  · intro i hi h1 h2; exec_simp

theorem sCopy_spec {o x : SInt} {t : ℕ} (ho : o.Below t) (hx : x.Below t) (hne : o.sign ≠ o.mag)
    {ρ : ℕ → ℕ} {zx : ℤ} (rx : ReprInt ρ x zx) : SContract (sCopy o x t) o t ρ zx := by
  obtain ⟨hos, hom⟩ := ho; obtain ⟨hxs, hxm⟩ := hx
  obtain ⟨rxs, rxm⟩ := rx
  have rxs' : (ρ x.sign = 1 ∧ zx < 0) ∨ (ρ x.sign = 0 ∧ 0 ≤ zx) := by split_ifs at rxs <;> omega
  clear rxs
  refine SContract.of_execF (by simp [sCopy, Stmt.Plain]) ?_ ?_ ?_
  all_goals simp only [sCopy]; exec_simp
  · split_ifs <;> omega
  · omega
  · intro i hi h1 h2; exec_simp

theorem sNeg_spec {o x : SInt} {t : ℕ} (ho : o.Below t) (hx : x.Below t) (hne : o.sign ≠ o.mag)
    {ρ : ℕ → ℕ} {zx : ℤ} (rx : ReprInt ρ x zx) : SContract (sNeg o x t) o t ρ (-zx) := by
  obtain ⟨hos, hom⟩ := ho; obtain ⟨hxs, hxm⟩ := hx
  obtain ⟨rxs, rxm⟩ := rx
  have rxs' : (ρ x.sign = 1 ∧ zx < 0) ∨ (ρ x.sign = 0 ∧ 0 ≤ zx) := by split_ifs at rxs <;> omega
  clear rxs
  refine SContract.of_execF (by simp [sNeg, normSign, Stmt.Plain]) ?_ ?_ ?_
  all_goals simp only [sNeg, normSign]; exec_simp
  · split_ifs <;> omega
  · omega
  · intro i hi h1 h2; exec_simp

theorem sAbs_spec {o x : SInt} {t : ℕ} (ho : o.Below t) (hx : x.Below t) (hne : o.sign ≠ o.mag)
    {ρ : ℕ → ℕ} {zx : ℤ} (rx : ReprInt ρ x zx) : SContract (sAbs o x t) o t ρ |zx| := by
  obtain ⟨hos, hom⟩ := ho; obtain ⟨hxs, hxm⟩ := hx
  obtain ⟨rxs, rxm⟩ := rx
  have rxs' : (ρ x.sign = 1 ∧ zx < 0) ∨ (ρ x.sign = 0 ∧ 0 ≤ zx) := by split_ifs at rxs <;> omega
  clear rxs
  refine SContract.of_execF (by simp [sAbs, Stmt.Plain]) ?_ ?_ ?_
  all_goals simp only [sAbs]; exec_simp
  · rw [Int.abs_eq_natAbs]; split_ifs <;> omega
  · rw [Int.abs_eq_natAbs]; omega
  · intro i hi h1 h2; exec_simp

theorem sMul_spec {o x y : SInt} {t : ℕ} (ho : o.Below t) (hx : x.Below t) (hy : y.Below t)
    (hne : o.sign ≠ o.mag) {ρ : ℕ → ℕ} {zx zy : ℤ} (rx : ReprInt ρ x zx) (ry : ReprInt ρ y zy) :
    SContract (sMul o x y t) o t ρ (zx * zy) := by
  obtain ⟨hos, hom⟩ := ho; obtain ⟨hxs, hxm⟩ := hx; obtain ⟨hys, hym⟩ := hy
  obtain ⟨rxs, rxm⟩ := rx
  have rxs' : (ρ x.sign = 1 ∧ zx < 0) ∨ (ρ x.sign = 0 ∧ 0 ≤ zx) := by split_ifs at rxs <;> omega
  clear rxs
  obtain ⟨rys, rym⟩ := ry
  have rys' : (ρ y.sign = 1 ∧ zy < 0) ∨ (ρ y.sign = 0 ∧ 0 ≤ zy) := by split_ifs at rys <;> omega
  clear rys
  refine SContract.of_execF (by simp [sMul, normSign, Stmt.Plain]) ?_ ?_ ?_
  all_goals simp only [sMul, normSign]; exec_simp
  · simp only [rxm, rym, Nat.mul_eq_zero, Int.natAbs_eq_zero, mul_neg_iff]
    split_ifs <;> omega
  · rw [rxm, rym, Int.natAbs_mul]
  · intro i hi h1 h2; exec_simp


theorem nOp_spec {o : SInt} {o' : Op} {t : ℕ} (ho : o.Below t) (hne : o.sign ≠ o.mag)
    (ρ : ℕ → ℕ) : SContract (nOp o o' t) o t ρ (o'.eval ρ : ℤ) := by
  obtain ⟨hos, hom⟩ := ho
  have ec : ∀ (k : ℕ) (ρ' : ℕ → ℕ), (Op.const k).eval ρ' = k := fun _ _ => rfl
  have ey : ∀ (y : ℕ) (ρ' : ℕ → ℕ), (Op.copy y).eval ρ' = ρ' y := fun _ _ => rfl
  refine SContract.of_execF (by simp [nOp, Stmt.Plain]) ?_ ?_ ?_
  all_goals simp (disch := omega) only [nOp, Stmt.execF, ec, ey, Function.update_self,
    Function.update_of_ne]
  · simp
  · simp
  · intro i hi h1 h2; simp (disch := omega) only [Function.update_of_ne]

theorem sDiv_eq (o x y : SInt) (t : ℕ) : sDiv o x y t = nOp o (.div x.mag y.mag) t := rfl
theorem sMod_eq (o x y : SInt) (t : ℕ) : sMod o x y t = nOp o (.mod x.mag y.mag) t := rfl

theorem sDiv_spec {o x y : SInt} {t : ℕ} (ho : o.Below t) (hne : o.sign ≠ o.mag)
    {ρ : ℕ → ℕ} {zx zy : ℤ} (rx : ReprInt ρ x zx) (ry : ReprInt ρ y zy) :
    SContract (sDiv o x y t) o t ρ ((zx.natAbs / zy.natAbs : ℕ) : ℤ) := by
  have := nOp_spec (o' := .div x.mag y.mag) ho hne ρ
  rwa [Op.eval, rx.2, ry.2] at this

theorem sMod_spec {o x y : SInt} {t : ℕ} (ho : o.Below t) (hne : o.sign ≠ o.mag)
    {ρ : ℕ → ℕ} {zx zy : ℤ} (rx : ReprInt ρ x zx) (ry : ReprInt ρ y zy) :
    SContract (sMod o x y t) o t ρ ((zx.natAbs % zy.natAbs : ℕ) : ℤ) := by
  have := nOp_spec (o' := .mod x.mag y.mag) ho hne ρ
  rwa [Op.eval, rx.2, ry.2] at this

theorem sSub_spec {o x y : SInt} {t : ℕ} (ho : o.Below t) (hx : x.Below t) (hy : y.Below t)
    (hne : o.sign ≠ o.mag) {ρ : ℕ → ℕ} {zx zy : ℤ} (rx : ReprInt ρ x zx) (ry : ReprInt ρ y zy) :
    SContract (sSub o x y t) o t ρ (zx - zy) := by
  have b2 : ∀ {u : SInt}, u.Below t → u.Below (t + 2) := fun h => ⟨by have := h.1; omega,
    by have := h.2; omega⟩
  obtain ⟨ρ₁, h₁, r₁, f₁⟩ := sNeg_spec (o := ⟨t, t + 1⟩) (t := t + 2) ⟨by simp, by simp⟩ (b2 hy)
    (by simp) ry
  have rx₁ : ReprInt ρ₁ x zx := by
    obtain ⟨hxs, hxm⟩ := hx
    exact ⟨by rw [f₁ _ (by omega) (by simp; omega) (by simp; omega)]; exact rx.1,
      by rw [f₁ _ (by omega) (by simp; omega) (by simp; omega)]; exact rx.2⟩
  obtain ⟨ρ₂, h₂, r₂, f₂⟩ := sAdd_spec (b2 ho) (b2 hx) ⟨by simp, by simp⟩ hne rx₁ r₁
  refine ⟨ρ₂, BigStep.seqNormal h₁ h₂, by rwa [sub_eq_add_neg], fun i hi h1 h2 => ?_⟩
  rw [f₂ i (by omega) h1 h2, f₁ i (by omega) (by simp; omega) (by simp; omega)]

/-- The contract of a flag computation. -/
def FlagContract (S : Stmt) (f : ℕ) (ρ : ℕ → ℕ) (P : Prop) [Decidable P] : Prop :=
  S.Plain ∧ S.execF ρ f = (if P then 1 else 0) ∧ ∀ i, i ≠ f → S.execF ρ i = ρ i

theorem sLtFlag_spec {f : ℕ} {x y : SInt}
    (hf : f ≠ x.sign ∧ f ≠ x.mag ∧ f ≠ y.sign ∧ f ≠ y.mag) {ρ : ℕ → ℕ} {zx zy : ℤ}
    (rx : ReprInt ρ x zx) (ry : ReprInt ρ y zy) : FlagContract (sLtFlag f x y) f ρ (zx < zy) := by
  obtain ⟨rxs, rxm⟩ := rx
  have rxs' : (ρ x.sign = 1 ∧ zx < 0) ∨ (ρ x.sign = 0 ∧ 0 ≤ zx) := by split_ifs at rxs <;> omega
  clear rxs
  obtain ⟨rys, rym⟩ := ry
  have rys' : (ρ y.sign = 1 ∧ zy < 0) ∨ (ρ y.sign = 0 ∧ 0 ≤ zy) := by split_ifs at rys <;> omega
  clear rys
  refine ⟨by simp [sLtFlag, Stmt.Plain], ?_, ?_⟩
  · simp only [sLtFlag]; exec_simp
    split_ifs <;> omega
  · intro i hi; simp only [sLtFlag]; exec_simp
    split_ifs <;> exec_simp

theorem sEqFlag_spec {f : ℕ} {x y : SInt}
    (hf : f ≠ x.sign ∧ f ≠ x.mag ∧ f ≠ y.sign ∧ f ≠ y.mag) {ρ : ℕ → ℕ} {zx zy : ℤ}
    (rx : ReprInt ρ x zx) (ry : ReprInt ρ y zy) : FlagContract (sEqFlag f x y) f ρ (zx = zy) := by
  obtain ⟨rxs, rxm⟩ := rx
  have rxs' : (ρ x.sign = 1 ∧ zx < 0) ∨ (ρ x.sign = 0 ∧ 0 ≤ zx) := by split_ifs at rxs <;> omega
  clear rxs
  obtain ⟨rys, rym⟩ := ry
  have rys' : (ρ y.sign = 1 ∧ zy < 0) ∨ (ρ y.sign = 0 ∧ 0 ≤ zy) := by split_ifs at rys <;> omega
  clear rys
  refine ⟨by simp [sEqFlag, Stmt.Plain], ?_, ?_⟩
  · simp only [sEqFlag]; exec_simp
    split_ifs <;> omega
  · intro i hi; simp only [sEqFlag]; exec_simp
    split_ifs <;> exec_simp

end ZInQ.Compiler.IR
