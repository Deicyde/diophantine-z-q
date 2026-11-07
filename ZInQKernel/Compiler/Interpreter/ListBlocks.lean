import ZInQKernel.Compiler.Interpreter.Blocks
import ZInQKernel.Compiler.Interpreter.TapeLists

/-!
# List blocks of the interpreter

`unconsBlock x h t b` computes `(h, t) = uncons x` (so `(0, 0)` for `x = nil`) by halving a
private copy of `x` while it is even, each halving strictly decreasing it; `consBlock h t out b`
computes `out = cons h t = 2 ^ h (2t + 1)`, copying both inputs before the final write, so that
`out` may be one of the inputs. Both leave every register outside their outputs and scratch
registers unchanged.

(Blueprint: `compiler/natural/universal/interpreter-list-primitives.md`.)
-/

namespace ZInQ.Compiler.Universal

open RM Stmt

/-! ### Doubling loops -/

/-- The doubling loop `while c { x ← x + x }`. -/
theorem runs_doubleLoop {c x s t₁ t₂ : ℕ} (hcx : c ≠ x) (hcs : c ≠ s) (hct₁ : c ≠ t₁)
    (hct₂ : c ≠ t₂) (hxs : x ≠ s) (hxt₁ : x ≠ t₁) (hxt₂ : x ≠ t₂) (hst₁ : s ≠ t₁)
    (hst₂ : s ≠ t₂) (hx : x ≠ J) (hs : s ≠ J) (ht₁ : t₁ ≠ J) (ht₂ : t₂ ≠ J) (hc : c ≠ J) :
    ∀ σ : Regs, σ J = 0 → ∃ σ', Runs (whileDec c (doubleBlock x s t₁ t₂)) σ σ' ∧
      σ' x = 2 ^ σ c * σ x ∧ σ' c = 0 ∧
      Frame (fun k => k = c ∨ k = x ∨ k = s ∨ k = t₁ ∨ k = t₂) σ σ' := by
  suffices ∀ n (σ : Regs), σ c = n → σ J = 0 →
      ∃ σ', Runs (whileDec c (doubleBlock x s t₁ t₂)) σ σ' ∧
      σ' x = 2 ^ σ c * σ x ∧ σ' c = 0 ∧
      Frame (fun k => k = c ∨ k = x ∨ k = s ∨ k = t₁ ∨ k = t₂) σ σ' from
    fun σ => this _ σ rfl
  intro n
  induction n with
  | zero =>
    intro σ hσ _
    exact ⟨σ, Exec.while_zero hσ, by simp [hσ], hσ, Frame.refl _ _⟩
  | succ n ih =>
    intro σ hσ hJ
    set σ₁ := Function.update σ c (σ c - 1) with hσ₁
    have hσ₁J : σ₁ J = 0 := by rw [hσ₁]; upd; exact hJ
    have hd := runs_doubleBlock hxs hxt₁ hxt₂ hst₁ hst₂ hx hs ht₁ ht₂ σ₁ hσ₁J
    set σ₂ := Function.update (Function.update (Function.update (Function.update σ₁ s (σ₁ x)) t₁ 0)
      x (σ₁ x + σ₁ x)) t₂ 0 with hσ₂
    have hσ₂J : σ₂ J = 0 := by rw [hσ₂, hσ₁]; upd; exact hJ
    have hσ₂c : σ₂ c = n := by rw [hσ₂, hσ₁]; upd; omega
    obtain ⟨σ', hrun, hx', hc', hfr⟩ := ih σ₂ hσ₂c hσ₂J
    refine ⟨σ', Exec.while_normal (by omega) hd hrun, ?_, hc', ?_⟩
    · rw [hx', hσ₂c, hσ, hσ₂, hσ₁]; upd; rw [pow_succ]; ring
    · intro k hk
      simp only [not_or] at hk
      rw [hfr k (by simp only [not_or]; exact hk), hσ₂, hσ₁]; upd

/-! ### uncons -/

/-- The halving loop of `unconsBlock`: with `x = 2 ^ h · v` and `v > 0` in register `b`, it
reaches `h = (uncons x).1` and `t = (uncons x).2`. -/
theorem runs_unconsLoop {x h t b : ℕ} (hhb : h < b ∨ b + 8 ≤ h) (htb : t < b ∨ b + 8 ≤ t)
    (hJb : J < b) (hht : h ≠ t) (hhJ : h ≠ J) (htJ : t ≠ J) (ρ : Regs) (hJ : ρ J = 0) :
    ∀ σ : Regs, Frame (fun k => k = h ∨ k = t ∨ Scratch b 8 k) ρ σ → 0 < σ b →
      ρ x = 2 ^ σ h * σ b →
      ∃ σ', Runs (loop (seqs [copyBlock (b + 4) b (b + 5), clear (b + 1),
          divmod2 (b + 4) (b + 1) (b + 2),
          ifNZ (b + 2) (seqs [copyBlock t (b + 1) (b + 6), brk])
            (seqs [inc h, copyBlock b (b + 1) (b + 7), cont])])) σ σ' ∧
        Frame (fun k => k = h ∨ k = t ∨ Scratch b 8 k) ρ σ' ∧
        σ' h = (uncons (ρ x)).1 ∧ σ' t = (uncons (ρ x)).2 := by
  suffices ∀ n σ, σ b = n → Frame (fun k => k = h ∨ k = t ∨ Scratch b 8 k) ρ σ → 0 < σ b →
      ρ x = 2 ^ σ h * σ b →
      ∃ σ', Runs (loop (seqs [copyBlock (b + 4) b (b + 5), clear (b + 1),
          divmod2 (b + 4) (b + 1) (b + 2),
          ifNZ (b + 2) (seqs [copyBlock t (b + 1) (b + 6), brk])
            (seqs [inc h, copyBlock b (b + 1) (b + 7), cont])])) σ σ' ∧
        Frame (fun k => k = h ∨ k = t ∨ Scratch b 8 k) ρ σ' ∧
        σ' h = (uncons (ρ x)).1 ∧ σ' t = (uncons (ρ x)).2 from
    fun σ => this _ σ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hn hσ hpos hinv
    have hσJ : σ J = 0 := by rw [hσ J (by unfold Scratch; omega), hJ]
    have h1 := runs_copyBlock (x := b + 4) (y := b) (t := b + 5) (by omega) (by omega) (by omega)
      (by omega) (by omega) σ hσJ
    set σ₁ := Function.update (Function.update σ (b + 4) (σ b)) (b + 5) 0 with hσ₁
    have h2 := runs_clear (b + 1) σ₁
    set σ₂ := Function.update σ₁ (b + 1) 0 with hσ₂
    have h3 : Runs (divmod2 (b + 4) (b + 1) (b + 2)) σ₂ _ :=
      Exec.divmod2 (by omega) (by omega) (by omega) (by omega) (by omega)
    set σ₃ := Function.update (Function.update (Function.update σ₂ (b + 4) 0) (b + 1)
      (σ₂ (b + 1) + σ₂ (b + 4) / 2)) (b + 2) (σ₂ (b + 4) % 2) with hσ₃
    have e3q : σ₃ (b + 1) = σ b / 2 := by rw [hσ₃, hσ₂, hσ₁]; upd; omega
    have e3r : σ₃ (b + 2) = σ b % 2 := by rw [hσ₃, hσ₂, hσ₁]; upd
    have hσ₃J : σ₃ J = 0 := by rw [hσ₃, hσ₂, hσ₁]; upd; exact hσJ
    have hfr₃ : Frame (fun k => k = h ∨ k = t ∨ Scratch b 8 k) ρ σ₃ := by
      rw [hσ₃, hσ₂, hσ₁]
      repeat (refine Frame.upd (Or.inr (Or.inr ⟨by omega, by omega⟩)) _ ?_)
      exact hσ
    have e3h : σ₃ h = σ h := by rw [hσ₃, hσ₂, hσ₁]; upd
    by_cases hodd : σ b % 2 = 1
    · -- odd: the tail is the halving quotient
      have h4 := runs_copyBlock (x := t) (y := b + 1) (t := b + 6) (by omega) (by omega)
        (by omega) (by omega) (by omega) σ₃ hσ₃J
      set σ₄ := Function.update (Function.update σ₃ t (σ₃ (b + 1))) (b + 6) 0 with hσ₄
      have hbody : Exec (seqs [copyBlock (b + 4) b (b + 5), clear (b + 1),
          divmod2 (b + 4) (b + 1) (b + 2),
          ifNZ (b + 2) (seqs [copyBlock t (b + 1) (b + 6), brk])
            (seqs [inc h, copyBlock b (b + 1) (b + 7), cont])]) σ (.brk σ₄) :=
        Exec.seqs_cons h1 (Exec.seqs_cons h2 (Exec.seqs_cons h3 (Exec.seqs_abnormal
          (Exec.ifNZ_pos (by rw [e3r]; omega)
            (Exec.seqs_cons h4 (Exec.seqs_abnormal (Exec.brk _) trivial))) trivial)))
      have hx : ρ x = cons (σ h) (σ b / 2) := by rw [hinv, cons]; congr 1; omega
      refine ⟨σ₄, Exec.loop_brk hbody, ?_, ?_, ?_⟩
      · rw [hσ₄]
        refine Frame.upd (Or.inr (Or.inr ⟨by omega, by omega⟩)) _ ?_
        exact Frame.upd (Or.inr (Or.inl rfl)) _ hfr₃
      · rw [hσ₄]; upd; rw [e3h, hx, uncons_cons]
      · rw [hσ₄]; upd; rw [e3q, hx, uncons_cons]
    · -- even: count a halving and continue with the quotient
      have hev : σ b % 2 = 0 := by omega
      have h4 := runs_inc hhJ σ₃
      set σ₄ := Function.update σ₃ h (σ₃ h + 1) with hσ₄
      have hσ₄J : σ₄ J = 0 := by rw [hσ₄]; upd; exact hσ₃J
      have h5 := runs_copyBlock (x := b) (y := b + 1) (t := b + 7) (by omega) (by omega)
        (by omega) (by omega) (by omega) σ₄ hσ₄J
      set σ₅ := Function.update (Function.update σ₄ b (σ₄ (b + 1))) (b + 7) 0 with hσ₅
      have hbody : Exec (seqs [copyBlock (b + 4) b (b + 5), clear (b + 1),
          divmod2 (b + 4) (b + 1) (b + 2),
          ifNZ (b + 2) (seqs [copyBlock t (b + 1) (b + 6), brk])
            (seqs [inc h, copyBlock b (b + 1) (b + 7), cont])]) σ (.cont σ₅) :=
        Exec.seqs_cons h1 (Exec.seqs_cons h2 (Exec.seqs_cons h3 (Exec.seqs_abnormal
          (Exec.ifNZ_zero (by rw [e3r]; omega)
            (Exec.seqs_cons h4 (Exec.seqs_cons h5 (Exec.seqs_abnormal (Exec.cont _) trivial))))
          trivial)))
      have e5b : σ₅ b = σ b / 2 := by rw [hσ₅, hσ₄]; upd; exact e3q
      have e5h : σ₅ h = σ h + 1 := by rw [hσ₅, hσ₄]; upd; rw [e3h]
      have hfr₅ : Frame (fun k => k = h ∨ k = t ∨ Scratch b 8 k) ρ σ₅ := by
        rw [hσ₅]
        refine Frame.upd (Or.inr (Or.inr ⟨by omega, by omega⟩)) _ ?_
        refine Frame.upd (Or.inr (Or.inr ⟨by omega, by omega⟩)) _ ?_
        exact Frame.upd (Or.inl rfl) _ hfr₃
      obtain ⟨σ', hrun, hfr, hh, ht⟩ := ih (σ₅ b) (by rw [e5b]; omega) σ₅ rfl hfr₅
        (by rw [e5b]; omega) (by rw [e5b, e5h, hinv, pow_succ]; rw [mul_assoc]; congr 1; omega)
      exact ⟨σ', Exec.loop_cont hbody hrun, hfr, hh, ht⟩

/-- **uncons**: `(h, t) ← uncons x`, with `(0, 0)` for `x = nil`; scratch `b, …, b + 7`. -/
theorem runs_unconsBlock {x h t b : ℕ} (hxb : x < b ∨ b + 8 ≤ x) (hhb : h < b ∨ b + 8 ≤ h)
    (htb : t < b ∨ b + 8 ≤ t) (hJb : J < b) (hht : h ≠ t) (hhJ : h ≠ J) (htJ : t ≠ J)
    (hxh : x ≠ h) (hxt : x ≠ t) (ρ : Regs) (hJ : ρ J = 0) :
    ∃ ρ', Runs (unconsBlock x h t b) ρ ρ' ∧ ρ' h = (uncons (ρ x)).1 ∧
      ρ' t = (uncons (ρ x)).2 ∧ Frame (fun k => k = h ∨ k = t ∨ Scratch b 8 k) ρ ρ' := by
  have h1 := runs_copyBlock (x := b) (y := x) (t := b + 3) (by omega) (by omega) (by omega)
    (by omega) (by omega) ρ hJ
  set ρ₁ := Function.update (Function.update ρ b (ρ x)) (b + 3) 0 with hρ₁
  have h2 := runs_clear h ρ₁
  set ρ₂ := Function.update ρ₁ h 0 with hρ₂
  have hfr₂ : Frame (fun k => k = h ∨ k = t ∨ Scratch b 8 k) ρ ρ₂ := by
    rw [hρ₂, hρ₁]
    refine Frame.upd (Or.inl rfl) _ ?_
    refine Frame.upd (Or.inr (Or.inr ⟨by omega, by omega⟩)) _ ?_
    exact Frame.upd (Or.inr (Or.inr ⟨by omega, by omega⟩)) _ (Frame.refl _ _)
  have e2b : ρ₂ b = ρ x := by rw [hρ₂, hρ₁]; upd
  by_cases hx0 : ρ x = 0
  · refine ⟨Function.update ρ₂ t 0, h1.seqs_cons (h2.seqs_cons (Runs.seqs_one
      (Exec.ifNZ_zero (by rw [e2b, hx0]) (runs_clear t ρ₂)))), ?_, ?_, ?_⟩
    · upd; rw [hρ₂]; upd; simp [hx0]
    · upd; simp [hx0]
    · exact Frame.upd (Or.inr (Or.inl rfl)) _ hfr₂
  · obtain ⟨σ', hrun, hfr, hh, ht⟩ := runs_unconsLoop (x := x) hhb htb hJb hht hhJ htJ ρ hJ ρ₂ hfr₂
      (by rw [e2b]; omega) (by rw [e2b, hρ₂]; upd; simp)
    exact ⟨σ', h1.seqs_cons (h2.seqs_cons (Runs.seqs_one (Exec.ifNZ_pos (by rw [e2b]; exact hx0)
      hrun))), hh, ht, hfr⟩

/-! ### cons -/

/-- **cons**: `out ← cons h t = 2 ^ h (2t + 1)`, both inputs being copied before the final
write; scratch `b, …, b + 10`. The tail may be the jump register (`nil`). -/
theorem runs_consBlock {h t out b : ℕ} (hhb : h < b ∨ b + 11 ≤ h) (htb : t < b ∨ b + 11 ≤ t)
    (houtb : out < b ∨ b + 11 ≤ out) (hJb : J < b) (houtJ : out ≠ J) (ρ : Regs)
    (hJ : ρ J = 0) :
    ∃ ρ', Runs (consBlock h t out b) ρ ρ' ∧ ρ' out = cons (ρ h) (ρ t) ∧
      Frame (fun k => k = out ∨ Scratch b 11 k) ρ ρ' := by
  have h1 := runs_copyBlock (x := b) (y := t) (t := b + 2) (by omega) (by omega) (by omega)
    (by omega) (by omega) ρ hJ
  set ρ₁ := Function.update (Function.update ρ b (ρ t)) (b + 2) 0 with hρ₁
  have hρ₁J : ρ₁ J = 0 := by rw [hρ₁]; upd; exact hJ
  have h2 := runs_doubleBlock (x := b) (s := b + 3) (t₁ := b + 4) (t₂ := b + 5) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ρ₁ hρ₁J
  set ρ₂ := Function.update (Function.update (Function.update (Function.update ρ₁ (b + 3)
    (ρ₁ b)) (b + 4) 0) b (ρ₁ b + ρ₁ b)) (b + 5) 0 with hρ₂
  have h3 := runs_inc (x := b) (by omega) ρ₂
  set ρ₃ := Function.update ρ₂ b (ρ₂ b + 1) with hρ₃
  have hρ₃J : ρ₃ J = 0 := by rw [hρ₃, hρ₂, hρ₁]; upd; exact hJ
  have h4 := runs_copyBlock (x := b + 1) (y := h) (t := b + 6) (by omega) (by omega) (by omega)
    (by omega) (by omega) ρ₃ hρ₃J
  set ρ₄ := Function.update (Function.update ρ₃ (b + 1) (ρ₃ h)) (b + 6) 0 with hρ₄
  have hρ₄J : ρ₄ J = 0 := by rw [hρ₄, hρ₃, hρ₂, hρ₁]; upd; exact hJ
  obtain ⟨ρ₅, h5, e5b, -, hfr₅⟩ := runs_doubleLoop (c := b + 1) (x := b) (s := b + 7)
    (t₁ := b + 8) (t₂ := b + 9) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) ρ₄ hρ₄J
  have hρ₅J : ρ₅ J = 0 := by
    rw [hfr₅ J (by omega), hρ₄, hρ₃, hρ₂, hρ₁]; upd; exact hJ
  have h6 := runs_copyBlock (x := out) (y := b) (t := b + 10) (by omega) (by omega) (by omega)
    (by omega) (by omega) ρ₅ hρ₅J
  refine ⟨_, h1.seqs_cons (h2.seqs_cons (h3.seqs_cons (h4.seqs_cons (h5.seqs_cons
    h6.seqs_one)))), ?_, ?_⟩
  · upd
    rw [e5b, hρ₄]; upd
    have eh : ρ₃ h = ρ h := by rw [hρ₃, hρ₂, hρ₁]; upd
    have eb : ρ₃ b = 2 * ρ t + 1 := by rw [hρ₃, hρ₂, hρ₁]; upd; ring
    rw [eh, eb, cons]
  · intro k hk
    simp only [not_or, Scratch] at hk
    upd
    rw [hfr₅ k (by omega), hρ₄, hρ₃, hρ₂, hρ₁]; upd

end ZInQ.Compiler.Universal
