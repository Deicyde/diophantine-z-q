import ZInQKernel.Compiler.Programs.Lowering

/-!
# Correctness of the primitive blocks

Each block of the lowering, entered with the jump register and the auxiliary registers zero,
reaches its exit with the target register updated and every other register restored. The
register files are written as explicit functions `fun i => if … then … else σ i`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace ZInQ.Compiler.IR

open RM

theorem Embedded.split {μ : Machine} {s : ℕ} {l₁ l₂ : List Instr} (h : Embedded μ s (l₁ ++ l₂)) :
    Embedded μ s l₁ ∧ Embedded μ (s + l₁.length) l₂ := ⟨h.append_left, h.append_right⟩

theorem Embedded.shift {μ : Machine} {s s' : ℕ} {l : List Instr} (h : Embedded μ s l)
    (e : s = s') : Embedded μ s' l := e ▸ h

theorem Reaches.regs_eq {μ : Machine} {c : Config} {s : ℕ} {f g : ℕ → ℕ}
    (h : Reaches μ c ⟨s, f⟩) (e : f = g) : Reaches μ c ⟨s, g⟩ := e ▸ h

theorem Reaches.state_eq {μ : Machine} {c : Config} {s s' : ℕ} {f : ℕ → ℕ}
    (h : Reaches μ c ⟨s, f⟩) (e : s = s') : Reaches μ c ⟨s', f⟩ := e ▸ h

theorem Reaches.trans' {μ : Machine} {c d : Config} {s₁ s₂ : ℕ} {f : ℕ → ℕ}
    (h₁ : Reaches μ c ⟨s₁, f⟩) (h₂ : Reaches μ ⟨s₂, f⟩ d) (e : s₁ = s₂) : Reaches μ c d :=
  h₁.trans (e ▸ h₂)

/-- `omega` after unfolding the auxiliary registers. -/
macro "aomega" : tactic => `(tactic| ((try simp only [aux] at *) <;> omega))

@[simp] theorem clearB_length (x s : ℕ) : (clearB x s).length = 1 := rfl
@[simp] theorem transfer1_length (J y d s : ℕ) : (transfer1 J y d s).length = 3 := rfl
@[simp] theorem transfer2_length (J y d e s : ℕ) : (transfer2 J y d e s).length = 4 := rfl
@[simp] theorem snap_length (J y a b s : ℕ) : (snap J y a b s).length = 7 := rfl
@[simp] theorem snap2_length (J y z s : ℕ) : (snap2 J y z s).length = 14 := rfl
@[simp] theorem incs_length (x k s : ℕ) : (incs x k s).length = k := by simp [incs]

theorem Embedded.clear {μ : Machine} {s x : ℕ} (he : Embedded μ s (clearB x s)) (σ : ℕ → ℕ) :
    Reaches μ ⟨s, σ⟩ ⟨s + 1, fun i => if i = x then 0 else σ i⟩ := by
  have h := he 0 (by simp); simp [clearB] at h
  refine (reaches_clear h σ).regs_eq ?_
  funext i; simp [Function.update_apply]

theorem Embedded.transfer1 {μ : Machine} {s J y d : ℕ} (he : Embedded μ s (transfer1 J y d s))
    (hyd : y ≠ d) (hJy : J ≠ y) (hJd : J ≠ d) (σ : ℕ → ℕ) (hJ : σ J = 0) :
    Reaches μ ⟨s, σ⟩ ⟨s + 3, fun i => if i = y then 0 else if i = d then σ d + σ y else σ i⟩ := by
  have h0 := he 0 (by simp); have h1 := he 1 (by simp); have h2 := he 2 (by simp)
  simp [IR.transfer1] at h0 h1 h2
  exact reaches_transfer1 h0 h1 h2 hyd hJy hJd σ hJ

theorem Embedded.transfer2 {μ : Machine} {s J y d e : ℕ}
    (he : Embedded μ s (transfer2 J y d e s)) (hyd : y ≠ d) (hye : y ≠ e) (hde : d ≠ e)
    (hJy : J ≠ y) (hJd : J ≠ d) (hJe : J ≠ e) (σ : ℕ → ℕ) (hJ : σ J = 0) :
    Reaches μ ⟨s, σ⟩ ⟨s + 4, fun i => if i = y then 0 else if i = d then σ d + σ y else
      if i = e then σ e + σ y else σ i⟩ := by
  have h0 := he 0 (by simp); have h1 := he 1 (by simp); have h2 := he 2 (by simp)
  have h3 := he 3 (by simp)
  simp [IR.transfer2] at h0 h1 h2 h3
  exact reaches_transfer2 h0 h1 h2 h3 hyd hye hde hJy hJd hJe σ hJ

theorem Embedded.snap {μ : Machine} {s J y a b : ℕ} (he : Embedded μ s (snap J y a b s))
    (hya : y ≠ a) (hyb : y ≠ b) (hab : a ≠ b) (hJy : J ≠ y) (hJa : J ≠ a) (hJb : J ≠ b)
    (σ : ℕ → ℕ) (hJ : σ J = 0) (ha : σ a = 0) (hb : σ b = 0) :
    Reaches μ ⟨s, σ⟩ ⟨s + 7, fun i => if i = a then σ y else σ i⟩ := by
  obtain ⟨he1, he2⟩ := he.split
  have r1 := he1.transfer2 hya hyb hab hJy hJa hJb σ hJ
  refine Reaches.regs_eq (Reaches.state_eq (r1.trans
    ((he2.shift (by simp)).transfer1 hyb.symm hJb hJy _ ?_)) (by omega)) ?_
  · simp [hJy, hJa, hJb, hJ]
  · funext i; simp only []
    split_ifs <;> subst_vars <;> simp_all


/-- Snapshots of `y` and `z` into `A₀` and `A₂`, then `x` cleared. -/
theorem Embedded.snap2Clear {μ : Machine} {s J x y z : ℕ}
    (he : Embedded μ s (snap2 J y z s ++ clearB x (s + 14))) (hx : x < J) (hy : y < J)
    (hz : z < J) (σ : ℕ → ℕ) (h0 : ∀ i, J ≤ i → σ i = 0) :
    Reaches μ ⟨s, σ⟩ ⟨s + 15, fun i => if i = x then 0 else if i = aux J 2 then σ z else
      if i = aux J 0 then σ y else σ i⟩ := by
  obtain ⟨he1, he3⟩ := he.split
  obtain ⟨he1, he2⟩ := he1.split
  have hJ := h0 J le_rfl
  have hA0 := h0 (aux J 0) (by aomega)
  have hA1 := h0 (aux J 1) (by aomega)
  have hA2 := h0 (aux J 2) (by aomega)
  refine Reaches.regs_eq (Reaches.state_eq ((he1.snap (by aomega) (by aomega) (by aomega)
    (by aomega) (by aomega) (by aomega) σ hJ hA0 hA1).trans' (Reaches.trans'
      ((he2.shift (by simp)).snap (by aomega) (by aomega) (by aomega) (by aomega) (by aomega)
        (by aomega) _ ?_ ?_ ?_) ((he3.shift (by simp)).clear _) (by omega)) (by omega))
        (by omega)) ?_
  · simp only [aux] at *; split_ifs <;> omega
  · simp only [aux] at *; split_ifs <;> omega
  · simp only [aux] at *; split_ifs <;> omega
  · funext i; simp only [aux] at *
    split_ifs <;> subst_vars <;> omega

theorem assignB_copy {μ : Machine} {s J x y : ℕ} (hx : x < J) (hy : y < J)
    (he : Embedded μ s (assignB J x (.copy y) s)) (σ : ℕ → ℕ) (h0 : ∀ i, J ≤ i → σ i = 0) :
    Reaches μ ⟨s, σ⟩ ⟨s + 11, fun i => if i = x then σ y else σ i⟩ := by
  simp only [assignB] at he
  obtain ⟨he1, he3⟩ := he.split
  obtain ⟨he1, he2⟩ := he1.split
  have hJ := h0 J le_rfl
  have hA0 := h0 (aux J 0) (by aomega)
  have hA1 := h0 (aux J 1) (by aomega)
  refine Reaches.regs_eq (Reaches.state_eq ((he1.snap (by aomega) (by aomega) (by aomega)
    (by aomega) (by aomega) (by aomega) σ hJ hA0 hA1).trans' (Reaches.trans'
      ((he2.shift (by simp)).clear _)
      ((he3.shift (by simp)).transfer1 (by aomega) (by aomega) (by aomega) _ ?_) (by omega))
      (by omega)) (by omega)) ?_
  · simp only [aux] at *; split_ifs <;> omega
  · funext i; simp only [aux] at *
    split_ifs <;> subst_vars <;> omega

theorem assignB_add {μ : Machine} {s J x y z : ℕ} (hx : x < J) (hy : y < J) (hz : z < J)
    (he : Embedded μ s (assignB J x (.add y z) s)) (σ : ℕ → ℕ) (h0 : ∀ i, J ≤ i → σ i = 0) :
    Reaches μ ⟨s, σ⟩ ⟨s + 21, fun i => if i = x then σ y + σ z else σ i⟩ := by
  simp only [assignB] at he
  obtain ⟨he1, he3⟩ := he.split
  obtain ⟨he1, he2⟩ := he1.split
  have hJ := h0 J le_rfl
  have hA0 := h0 (aux J 0) (by aomega)
  have hA2 := h0 (aux J 2) (by aomega)
  refine Reaches.regs_eq (Reaches.state_eq ((he1.snap2Clear hx hy hz σ h0).trans' (Reaches.trans'
    ((he2.shift (by simp)).transfer1 (by aomega) (by aomega) (by aomega) _ ?_)
    ((he3.shift (by simp)).transfer1 (by aomega) (by aomega) (by aomega) _ ?_) (by omega))
      (by omega)) (by omega)) ?_
  · simp only [aux] at *; split_ifs <;> omega
  · simp only [aux] at *; split_ifs <;> omega
  · funext i; simp only [aux] at *
    split_ifs <;> subst_vars <;> omega


/-! ### Loops -/

/-- The saturating subtraction loop `dec a; dec x`. -/
theorem reaches_monus {μ : Machine} {s a x : ℕ} (h0 : μ s = .dec a (s + 1) (s + 2))
    (h1 : μ (s + 1) = .dec x s s) (hax : a ≠ x) (σ : ℕ → ℕ) :
    Reaches μ ⟨s, σ⟩ ⟨s + 2, fun i => if i = a then 0 else if i = x then σ x - σ a else σ i⟩ := by
  induction hn : σ a generalizing σ with
  | zero =>
    refine ((Reaches.refl _ _).of_step (step_dec_zero h0 hn)).regs_eq ?_
    funext i; split_ifs <;> subst_vars <;> omega
  | succ n ih =>
    have e1 := step_dec_pos h0 (σ := σ) (by omega)
    by_cases hx : Function.update σ a (σ a - 1) x = 0
    · have e2 := step_dec_zero h1 hx
      refine (Reaches.of_step e1 (Reaches.of_step e2 (ih _ ?_))).regs_eq ?_
      · simp; omega
      · funext i; simp [Function.update_apply] at hx ⊢
        split_ifs <;> subst_vars <;> simp_all <;> omega
    · have e2 := step_dec_pos h1 hx
      refine (Reaches.of_step e1 (Reaches.of_step e2 (ih _ ?_))).regs_eq ?_
      · simp [Function.update_apply, hax]; omega
      · funext i; simp [Function.update_apply] at hx ⊢
        split_ifs <;> subst_vars <;> simp_all <;> omega

/-- The multiplication loop: `b` times, add `a` into `x` (through `t`, restoring `a`). -/
theorem reaches_mulLoop {μ : Machine} {s J a b x t : ℕ} (h0 : μ s = .dec b (s + 1) (s + 9))
    (he2 : Embedded μ (s + 1) (transfer2 J a x t (s + 1)))
    (he1 : Embedded μ (s + 5) (transfer1 J t a (s + 5))) (hj : μ (s + 8) = jmp J s)
    (hab : a ≠ b) (hax : a ≠ x) (hat : a ≠ t) (hbx : b ≠ x) (hbt : b ≠ t) (hxt : x ≠ t)
    (hJa : J ≠ a) (hJb : J ≠ b) (hJx : J ≠ x) (hJt : J ≠ t) (σ : ℕ → ℕ) (hJ : σ J = 0)
    (ht : σ t = 0) :
    Reaches μ ⟨s, σ⟩ ⟨s + 9, fun i => if i = b then 0 else if i = x then σ x + σ a * σ b else
      σ i⟩ := by
  induction hn : σ b generalizing σ with
  | zero =>
    refine ((Reaches.refl _ _).of_step (step_dec_zero h0 hn)).regs_eq ?_
    funext i; split_ifs <;> subst_vars <;> simp_all
  | succ n ih =>
    have e1 := step_dec_pos h0 (σ := σ) (by omega)
    refine Reaches.of_step e1 (Reaches.trans' (he2.transfer2 hax hat hxt hJa hJx hJt _ ?_)
      (Reaches.trans' (he1.transfer1 hat.symm hJt hJa _ ?_) (Reaches.of_step (step_jmp hj ?_)
        (ih _ ?_ ?_ ?_)) (by omega)) (by omega)) |>.regs_eq ?_
    all_goals simp [Function.update_apply, hab, hab.symm, hax, hat, hbx, hbt, hxt, hJa, hJb, hJx,
      hJt, hJ, ht, hax.symm, hat.symm, hbx.symm, hbt.symm, hxt.symm]
    · omega
    · funext i; split_ifs <;> subst_vars <;> simp_all; ring


/-- The division loop at `u`: with `r` the remainder still to process, `m + c = z`, `c ≥ 1`
and `q` the quotient so far, it ends with `r = 0`, `q ← q + (m + r) / z`,
`m ← (m + r) mod z`, `c ← z - m`. -/
theorem reaches_divLoop {μ : Machine} {u J r m c q zz t : ℕ}
    (h0 : μ u = .dec r (u + 1) (u + 15)) (h1 : μ (u + 1) = .inc m (u + 2))
    (h2 : μ (u + 2) = .dec c (u + 3) (u + 3)) (h3 : μ (u + 3) = .dec c (u + 4) (u + 5))
    (h4 : μ (u + 4) = .inc c u) (h5 : μ (u + 5) = .inc q (u + 6))
    (h6 : μ (u + 6) = .dec m (u + 6) (u + 6 + 1))
    (he7 : Embedded μ (u + 7) (transfer2 J zz c t (u + 7)))
    (he11 : Embedded μ (u + 11) (transfer1 J t zz (u + 11))) (h14 : μ (u + 14) = jmp J u)
    (hrm : r ≠ m) (hrc : r ≠ c) (hrq : r ≠ q) (hrz : r ≠ zz) (hrt : r ≠ t) (hmc : m ≠ c)
    (hmq : m ≠ q) (hmz : m ≠ zz) (hmt : m ≠ t) (hcq : c ≠ q) (hcz : c ≠ zz) (hct : c ≠ t)
    (hqz : q ≠ zz) (hqt : q ≠ t) (hzt : zz ≠ t) (hJr : J ≠ r) (hJm : J ≠ m) (hJc : J ≠ c)
    (hJq : J ≠ q) (hJz : J ≠ zz) (hJt : J ≠ t)
    (σ : ℕ → ℕ) (hJ : σ J = 0) (ht : σ t = 0) (hsum : σ m + σ c = σ zz) (hc : 0 < σ c) :
    Reaches μ ⟨u, σ⟩ ⟨u + 15, fun i => if i = r then 0 else
      if i = m then (σ m + σ r) % σ zz else if i = c then σ zz - (σ m + σ r) % σ zz else
      if i = q then σ q + (σ m + σ r) / σ zz else σ i⟩ := by
  induction hn : σ r generalizing σ with
  | zero =>
    refine ((Reaches.refl _ _).of_step (step_dec_zero h0 hn)).regs_eq ?_
    have hlt : σ m < σ zz := by omega
    funext i
    split_ifs <;> subst_vars <;> (try simp [hn, Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt]) <;> omega
  | succ n ih =>
    have hz : 0 < σ zz := by omega
    have e1 := step_dec_pos h0 (σ := σ) (by omega)
    have e2 := step_inc h1 (σ := Function.update σ r (σ r - 1))
    have e3 := step_dec_pos h2 (σ := Function.update (Function.update σ r (σ r - 1)) m
      (Function.update σ r (σ r - 1) m + 1)) (by simp [Function.update_apply, hmc.symm, hrc.symm]; omega)
    by_cases hc1 : σ c = 1
    · -- the group is complete: q ← q + 1, m ← 0, c ← z
      have e4 := step_dec_zero h3 (σ := Function.update (Function.update (Function.update σ r
        (σ r - 1)) m (Function.update σ r (σ r - 1) m + 1)) c (Function.update (Function.update σ r
        (σ r - 1)) m (Function.update σ r (σ r - 1) m + 1) c - 1))
        (by simp [Function.update_apply, hmc.symm, hrc.symm]; omega)
      refine Reaches.of_step e1 (Reaches.of_step e2 (Reaches.of_step e3 (Reaches.of_step e4
        (Reaches.of_step (step_inc h5) ((reaches_clear h6 _).trans' (Reaches.trans'
          (he7.transfer2 hcz.symm hzt hct hJz hJc hJt _ ?_) (Reaches.trans'
          (he11.transfer1 hzt.symm hJt hJz _ ?_) (Reaches.of_step (step_jmp h14 ?_)
            (ih _ ?_ ?_ ?_ ?_ ?_)) (by omega)) (by omega)) (by omega)))))) |>.regs_eq ?_
      all_goals simp [Function.update_apply, hrm, hrc, hrq, hrz, hrt, hmc, hmq, hmz, hmt, hcq, hcz,
        hct, hqz, hqt, hzt, hJr, hJm, hJc, hJq, hJz, hJt, hrm.symm, hrc.symm, hrq.symm, hrz.symm,
        hrt.symm, hmc.symm, hmq.symm, hmz.symm, hmt.symm, hcq.symm, hcz.symm, hct.symm, hqz.symm,
        hqt.symm, hzt.symm, hJ, ht]
      all_goals try omega
      have hm : σ m + 1 = σ zz := by omega
      have key : σ m + σ r = (σ r - 1) + σ zz := by omega
      funext i
      split_ifs <;> subst_vars <;> simp_all [Nat.add_mod_right, Nat.add_div_right _ hz] <;> omega
    · -- continue the group: m ← m + 1, c ← c - 1
      have e4 := step_dec_pos h3 (σ := Function.update (Function.update (Function.update σ r
        (σ r - 1)) m (Function.update σ r (σ r - 1) m + 1)) c (Function.update (Function.update σ r
        (σ r - 1)) m (Function.update σ r (σ r - 1) m + 1) c - 1))
        (by simp [Function.update_apply, hmc.symm, hrc.symm]; omega)
      refine Reaches.of_step e1 (Reaches.of_step e2 (Reaches.of_step e3 (Reaches.of_step e4
        (Reaches.of_step (step_inc h4) (ih _ ?_ ?_ ?_ ?_ ?_))))) |>.regs_eq ?_
      all_goals simp [Function.update_apply, hrm, hrc, hrq, hrz, hrt, hmc, hmq, hmz, hmt, hcq, hcz,
        hct, hqz, hqt, hzt, hJr, hJm, hJc, hJq, hJz, hJt, hrm.symm, hrc.symm, hrq.symm, hrz.symm,
        hrt.symm, hmc.symm, hmq.symm, hmz.symm, hmt.symm, hcq.symm, hcz.symm, hct.symm, hqz.symm,
        hqt.symm, hzt.symm, hJ, ht]
      all_goals try omega
      have key : σ m + 1 + (σ r - 1) = σ m + σ r := by omega
      funext i
      split_ifs <;> subst_vars <;> simp_all <;> omega


theorem reaches_incs {μ : Machine} {s x : ℕ} : ∀ (k : ℕ), Embedded μ (s + 1) (incs x k s) →
    ∀ σ : ℕ → ℕ, Reaches μ ⟨s + 1, σ⟩ ⟨s + 1 + k, fun i => if i = x then σ x + k else σ i⟩
  | 0, _, σ => (Reaches.refl _ _).regs_eq (by funext i; split_ifs <;> subst_vars <;> simp)
  | k + 1, he, σ => by
    have he' : Embedded μ (s + 1) (incs x k s ++ [.inc x (s + k + 2)]) := by
      simpa [incs, List.range_succ] using he
    obtain ⟨he1, he2⟩ := he'.split
    have h := he2.head
    simp only [incs_length] at h
    refine ((reaches_incs k he1 σ).trans ((Reaches.refl _ _).of_step (step_inc h))).state_eq
      (by omega) |>.regs_eq ?_
    funext i; simp [Function.update_apply]; split_ifs <;> omega

theorem assignB_const {μ : Machine} {s J x k : ℕ} (he : Embedded μ s (assignB J x (.const k) s))
    (σ : ℕ → ℕ) : Reaches μ ⟨s, σ⟩ ⟨s + (k + 1), fun i => if i = x then k else σ i⟩ := by
  simp only [assignB] at he
  obtain ⟨he1, he2⟩ := he.split
  refine ((he1.clear σ).trans (reaches_incs k (he2.shift (by simp)) _)).state_eq (by omega)
    |>.regs_eq ?_
  funext i; by_cases h : i = x <;> simp [h]

theorem assignB_sub {μ : Machine} {s J x y z : ℕ} (hx : x < J) (hy : y < J) (hz : z < J)
    (he : Embedded μ s (assignB J x (.sub y z) s)) (σ : ℕ → ℕ) (h0 : ∀ i, J ≤ i → σ i = 0) :
    Reaches μ ⟨s, σ⟩ ⟨s + 20, fun i => if i = x then σ y - σ z else σ i⟩ := by
  simp only [assignB] at he
  obtain ⟨he1, he3⟩ := he.split
  obtain ⟨he1, he2⟩ := he1.split
  have hJ := h0 J le_rfl
  have hA0 := h0 (aux J 0) (by aomega)
  have hA2 := h0 (aux J 2) (by aomega)
  have h18 := he3 0 (by simp); have h19 := he3 1 (by simp)
  simp only [List.length_append, snap2_length, clearB_length, transfer1_length] at h18 h19
  simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h18 h19
  refine Reaches.regs_eq (Reaches.state_eq ((he1.snap2Clear hx hy hz σ h0).trans' (Reaches.trans'
    ((he2.shift (by simp)).transfer1 (by aomega) (by aomega) (by aomega) _ ?_)
    (reaches_monus (s := s + 18) (by simpa using h18) (by simpa using h19) (by aomega) _)
      (by omega)) (by omega)) (by omega)) ?_
  · simp only [aux] at *; split_ifs <;> omega
  · funext i; simp only [aux] at *
    split_ifs <;> subst_vars <;> omega

theorem assignB_mul {μ : Machine} {s J x y z : ℕ} (hx : x < J) (hy : y < J) (hz : z < J)
    (he : Embedded μ s (assignB J x (.mul y z) s)) (σ : ℕ → ℕ) (h0 : ∀ i, J ≤ i → σ i = 0) :
    Reaches μ ⟨s, σ⟩ ⟨s + 25, fun i => if i = x then σ y * σ z else σ i⟩ := by
  simp only [assignB] at he
  obtain ⟨he, he7⟩ := he.split
  obtain ⟨he, he6⟩ := he.split
  obtain ⟨he, he5⟩ := he.split
  obtain ⟨he, he4⟩ := he.split
  obtain ⟨he1, he3⟩ := he.split
  have hJ := h0 J le_rfl
  have hA0 := h0 (aux J 0) (by aomega)
  have hA1 := h0 (aux J 1) (by aomega)
  have hA2 := h0 (aux J 2) (by aomega)
  simp only [List.length_append, snap2_length, clearB_length, transfer1_length,
    transfer2_length, List.length_cons, List.length_nil] at he3 he4 he5 he6 he7
  have h15 := he3.head
  have h23 := he6.head
  rw [show s + (14 + 1) = s + 15 by omega] at h15
  rw [show s + 16 = s + 15 + 1 by omega] at he4
  rw [show s + 20 = s + 15 + 5 by omega] at he5
  rw [show s + 15 = s + 15 + 0 by omega] at h23
  refine Reaches.regs_eq (Reaches.state_eq ((he1.snap2Clear hx hy hz σ h0).trans' (Reaches.trans'
    (reaches_mulLoop (s := s + 15) (J := J) (by simpa using h15) (he4.shift (by omega))
      (he5.shift (by omega)) (by simpa using h23) (by aomega) (by aomega) (by aomega) (by aomega)
      (by aomega) (by aomega) (by aomega) (by aomega) (by aomega) (by aomega) _ ?_ ?_)
    ((he7.shift (by omega)).clear _) (by omega)) (by omega)) (by omega)) ?_
  · simp only [aux] at *; split_ifs <;> omega
  · simp only [aux] at *; split_ifs <;> omega
  · funext i; simp only [aux, Nat.add_zero] at *
    split_ifs <;> subst_vars <;> (try simp) <;> omega


theorem divModB_eq (J x y z : ℕ) (isDiv : Bool) (s : ℕ) :
    divModB J x y z isDiv s =
      snap2 J y z s ++ (clearB x (s + 14) ++
      ([.dec (aux J 2) (s + 16) (s + 47), .inc (aux J 2) (s + 17)] ++
      (transfer2 J (aux J 2) (aux J 4) (aux J 1) (s + 17) ++
      (transfer1 J (aux J 1) (aux J 2) (s + 21) ++
      ([.dec (aux J 0) (s + 25) (s + 39), .inc (aux J 3) (s + 26), .dec (aux J 4) (s + 27) (s + 27),
        .dec (aux J 4) (s + 28) (s + 29), .inc (aux J 4) (s + 24), .inc (aux J 5) (s + 30)] ++
      (clearB (aux J 3) (s + 30) ++
      (transfer2 J (aux J 2) (aux J 4) (aux J 1) (s + 31) ++
      (transfer1 J (aux J 1) (aux J 2) (s + 35) ++
      ([jmp J (s + 24)] ++
      (transfer1 J (if isDiv then aux J 5 else aux J 3) x (s + 39) ++
      (clearB (aux J 3) (s + 42) ++ (clearB (aux J 4) (s + 43) ++ (clearB (aux J 5) (s + 44) ++
      (clearB (aux J 2) (s + 45) ++
      ([jmp J (s + 47 + (if isDiv then 1 else 3))] ++
      (if isDiv then clearB (aux J 0) (s + 47) else transfer1 J (aux J 0) x (s + 47))))))))))))))))) := by
  cases isDiv <;> simp [divModB]

set_option maxHeartbeats 2000000 in
theorem assignB_divMod {μ : Machine} {s J x y z : ℕ} (isDiv : Bool) (hx : x < J) (hy : y < J)
    (hz : z < J) (he : Embedded μ s (divModB J x y z isDiv s)) (σ : ℕ → ℕ)
    (h0 : ∀ i, J ≤ i → σ i = 0) :
    Reaches μ ⟨s, σ⟩ ⟨s + 47 + (if isDiv then 1 else 3), fun i => if i = x then
      (if isDiv then σ y / σ z else σ y % σ z) else σ i⟩ := by
  rw [divModB_eq] at he
  have hJ := h0 J le_rfl
  have hA := fun k (_ : k < 6) => h0 (aux J k) (by aomega)
  have hA0 := hA 0 (by omega); have hA1 := hA 1 (by omega); have hA2 := hA 2 (by omega)
  have hA3 := hA 3 (by omega); have hA4 := hA 4 (by omega); have hA5 := hA 5 (by omega)
  simp only [aux, Nat.add_zero] at hA0 hA1 hA2 hA3 hA4 hA5
  obtain ⟨he1, he⟩ := he.split; obtain ⟨he2, he⟩ := he.split
  obtain ⟨he3, he⟩ := he.split; obtain ⟨he4, he⟩ := he.split
  obtain ⟨he5, he⟩ := he.split; obtain ⟨he6, he⟩ := he.split
  obtain ⟨he7, he⟩ := he.split; obtain ⟨he8, he⟩ := he.split
  obtain ⟨he9, he⟩ := he.split; obtain ⟨he10, he⟩ := he.split
  obtain ⟨he11, he⟩ := he.split; obtain ⟨he12, he⟩ := he.split
  obtain ⟨he13, he⟩ := he.split; obtain ⟨he14, he⟩ := he.split
  obtain ⟨he15, he⟩ := he.split; obtain ⟨he16, he17⟩ := he.split
  simp only [List.length_append, snap2_length, clearB_length, transfer1_length,
    transfer2_length, List.length_cons, List.length_nil, Nat.add_assoc, Nat.reduceAdd] at he2 he3 he4 he5 he6 he7 he8 he9 he10 he11 he12 he13 he14 he15 he16 he17
  have r1 := Embedded.snap2Clear (μ := μ) (s := s) (x := x) (y := y) (z := z)
    (fun i hi => by
      rcases Nat.lt_or_ge i 14 with h | h
      · rw [List.getElem_append_left (by simpa using h)]; exact he1 i h
      · rw [List.getElem_append_right (by simpa using h)]
        have := he2 (i - 14) (by simp at hi ⊢; omega)
        simp only [snap2_length] at this ⊢
        rw [show s + i = s + 14 + (i - 14) by omega]; exact this) hx hy hz σ h0
  have h15 := he3 0 (by simp); have h16 := he3 1 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h15 h16
  have h24 := he6 0 (by simp); have h25 := he6 1 (by simp); have h26 := he6 2 (by simp)
  have h27 := he6 3 (by simp); have h28 := he6 4 (by simp); have h29 := he6 5 (by simp)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, Nat.add_zero] at h24 h25 h26 h27 h28 h29
  have h30 := he7.head; have h38 := he10.head; have h46 := he16.head
  by_cases hz0 : σ z = 0
  · -- zero divisor: `x` is `0` (division) or `y` (remainder)
    refine r1.trans (Reaches.of_step (step_dec_zero h15 (by simp only [aux] at *; split_ifs <;> omega)) ?_)
    cases isDiv
    · refine Reaches.regs_eq (Reaches.state_eq ((he17.shift (by omega)).transfer1 (by aomega)
        (by aomega) (by aomega) _ (by simp only [aux] at *; split_ifs <;> omega)) (by simp)) ?_
      funext i; simp only [aux, Nat.add_zero, hz0, Nat.mod_zero, Nat.div_zero, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> subst_vars <;> omega
    · refine Reaches.regs_eq (Reaches.state_eq ((he17.shift (by omega)).clear _) (by simp)) ?_
      funext i; simp only [aux, Nat.add_zero, hz0, Nat.mod_zero, Nat.div_zero, ↓reduceIte]
      split_ifs <;> subst_vars <;> omega
  · have hzp : 0 < σ z := Nat.pos_of_ne_zero hz0
    simp only [aux, Nat.add_zero] at *
    -- phase 2: the copy `c ← z`
    have p2a : Reaches μ ⟨s + 15, fun i => if i = x then 0 else if i = J + 1 + 2 then σ z else
        if i = J + 1 then σ y else σ i⟩ ⟨s + 17, fun i => if i = x then 0 else
        if i = J + 1 + 2 then σ z else if i = J + 1 then σ y else σ i⟩ := by
      refine Reaches.of_step (step_dec_pos h15 (by split_ifs <;> omega))
        (Reaches.of_step (step_inc h16) (Reaches.refl _ _)) |>.regs_eq ?_
      funext i; simp only [Function.update_apply]; split_ifs <;> subst_vars <;> omega
    have p2b := (he4.shift (show s + 17 = s + 17 by rfl)).transfer2 (J := J) (y := J + 1 + 2)
      (d := J + 1 + 4) (e := J + 1 + 1) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (fun i => if i = x then 0 else if i = J + 1 + 2 then σ z else
        if i = J + 1 then σ y else σ i) (by split_ifs <;> omega)
    have p2b' : Reaches μ ⟨s + 17, fun i => if i = x then 0 else if i = J + 1 + 2 then σ z else
        if i = J + 1 then σ y else σ i⟩ ⟨s + 21, fun i => if i = x then 0 else
        if i = J + 1 + 2 then 0 else if i = J + 1 + 4 then σ z else if i = J + 1 + 1 then σ z else
        if i = J + 1 then σ y else σ i⟩ := by
      refine p2b.state_eq (by omega) |>.regs_eq ?_
      funext i; simp only []; split_ifs <;> subst_vars <;> omega
    have p2c := (he5.shift (show s + 21 = s + 21 by rfl)).transfer1 (J := J) (y := J + 1 + 1)
      (d := J + 1 + 2) (by omega) (by omega) (by omega) (fun i => if i = x then 0 else
        if i = J + 1 + 2 then 0 else if i = J + 1 + 4 then σ z else if i = J + 1 + 1 then σ z else
        if i = J + 1 then σ y else σ i) (by split_ifs <;> omega)
    have p2 : Reaches μ ⟨s + 15, fun i => if i = x then 0 else if i = J + 1 + 2 then σ z else
        if i = J + 1 then σ y else σ i⟩ ⟨s + 24, fun i => if i = x then 0 else
        if i = J + 1 then σ y else if i = J + 1 + 2 then σ z else if i = J + 1 + 4 then σ z else
        σ i⟩ := by
      refine p2a.trans (p2b'.trans (p2c.state_eq (by omega))) |>.regs_eq ?_
      funext i; simp only []; split_ifs <;> subst_vars <;> omega
    -- phase 3: the loop
    obtain ⟨rr, hrr⟩ : ∃ v, σ y % σ z = v := ⟨_, rfl⟩
    obtain ⟨qq, hqq⟩ : ∃ v, σ y / σ z = v := ⟨_, rfl⟩
    rw [hrr, hqq]
    obtain ⟨σ2, hσ2⟩ : ∃ f : ℕ → ℕ, f = fun i => if i = x then 0 else
        if i = J + 1 then σ y else if i = J + 1 + 2 then σ z else if i = J + 1 + 4 then σ z else
        σ i := ⟨_, rfl⟩
    rw [← hσ2] at p2
    have q0 : σ2 (J + 1) = σ y := by simp only [hσ2]; split_ifs <;> omega
    have q3 : σ2 (J + 1 + 3) = 0 := by simp only [hσ2]; split_ifs <;> omega
    have q4 : σ2 (J + 1 + 4) = σ z := by simp only [hσ2]; split_ifs <;> omega
    have q5 : σ2 (J + 1 + 5) = 0 := by simp only [hσ2]; split_ifs <;> omega
    have q2 : σ2 (J + 1 + 2) = σ z := by simp only [hσ2]; split_ifs <;> omega
    have q1 : σ2 (J + 1 + 1) = 0 := by simp only [hσ2]; split_ifs <;> omega
    have qJ : σ2 J = 0 := by simp only [hσ2]; split_ifs <;> omega
    have p3 : Reaches μ ⟨s + 24, σ2⟩ ⟨s + 39, fun i => if i = x then 0 else if i = J + 1 then 0 else
        if i = J + 1 + 3 then rr else if i = J + 1 + 4 then σ z - rr else
        if i = J + 1 + 5 then qq else if i = J + 1 + 2 then σ z else σ i⟩ := by
      refine Reaches.state_eq (reaches_divLoop (u := s + 24) (J := J) (by simpa using h24)
          (by simpa using h25) (by simpa using h26) (by simpa using h27) (by simpa using h28)
          (by simpa using h29) (by simpa using h30)
          (by simpa [show s + 31 = s + 24 + 7 by omega] using he8)
          (by simpa [show s + 35 = s + 24 + 11 by omega] using he9)
          (by simpa using h38)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          σ2 qJ q1 (by rw [q3, q4, q2]; omega) (by rw [q4]; omega)) (by omega) |>.regs_eq ?_
      have r0 : σ2 (J + 3) = σ z := by simp only [hσ2]; split_ifs <;> omega
      have r6 : σ2 (J + 6) = 0 := by simp only [hσ2]; split_ifs <;> omega
      have r4 : σ2 (J + 4) = 0 := by simp only [hσ2]; split_ifs <;> omega
      have r1 : σ2 (J + 1) = σ y := by simp only [hσ2]; split_ifs <;> omega
      simp only [r0, r6, r4, r1, Nat.zero_add, hrr, hqq]
      clear * - hσ2 hx hy hz hzp hJ hA0 hA1 hA2 hA3 hA4 hA5
      subst hσ2; funext i; beta_reduce; split_ifs <;> subst_vars <;> omega
    -- phase 4: the result into `x`, the auxiliary registers cleared
    obtain ⟨σ3, hσ3⟩ : ∃ f : ℕ → ℕ, f = fun i => if i = x then 0 else if i = J + 1 then 0 else
        if i = J + 1 + 3 then rr else if i = J + 1 + 4 then σ z - rr else
        if i = J + 1 + 5 then qq else if i = J + 1 + 2 then σ z else σ i := ⟨_, rfl⟩
    rw [← hσ3] at p3
    have clears : ∀ σ' : ℕ → ℕ, Reaches μ ⟨s + 42, σ'⟩ ⟨s + 46, fun i => if i = J + 1 + 2 then 0
        else if i = J + 1 + 5 then 0 else if i = J + 1 + 4 then 0 else if i = J + 1 + 3 then 0
        else σ' i⟩ := fun σ' =>
      Reaches.trans' ((he12.shift (by omega)).clear _) (Reaches.trans'
          ((he13.shift (by omega)).clear _) (Reaches.trans' ((he14.shift (by omega)).clear _)
          (Reaches.state_eq ((he15.shift (by omega)).clear _) (by omega)) (by omega)) (by omega))
          (by omega)
    have p4 : Reaches μ ⟨s + 39, σ3⟩
        ⟨s + 46, fun i => if i = x then (if isDiv then qq else rr) else σ i⟩ := by
      cases isDiv
      · simp only [Bool.false_eq_true, ite_false] at he11
        refine Reaches.trans' ((he11.shift (by omega)).transfer1 (by omega) (by omega) (by omega)
          σ3 (by simp only [hσ3]; split_ifs <;> omega)) (clears _) (by omega) |>.regs_eq ?_
        have e1 : σ3 (J + 1 + 3) = rr := by simp only [hσ3]; split_ifs <;> omega
        have e2 : σ3 x = 0 := by simp only [hσ3]; split_ifs <;> omega
        simp only [e1, e2, Bool.false_eq_true, ite_false, Nat.zero_add]
        clear * - hσ3 hrr hx hy hz hzp hJ hA0 hA1 hA2 hA3 hA4 hA5
        subst hσ3 hrr; funext i; beta_reduce; split_ifs <;> subst_vars <;> omega
      · simp only [ite_true] at he11
        refine Reaches.trans' ((he11.shift (by omega)).transfer1 (by omega) (by omega) (by omega)
          σ3 (by simp only [hσ3]; split_ifs <;> omega)) (clears _) (by omega) |>.regs_eq ?_
        have e1 : σ3 (J + 1 + 5) = qq := by simp only [hσ3]; split_ifs <;> omega
        have e2 : σ3 x = 0 := by simp only [hσ3]; split_ifs <;> omega
        simp only [e1, e2, ite_true, Nat.zero_add]
        clear * - hσ3 hqq hx hy hz hzp hJ hA0 hA1 hA2 hA3 hA4 hA5
        subst hσ3 hqq; funext i; beta_reduce; split_ifs <;> subst_vars <;> omega
    refine r1.trans (p2.trans (p3.trans (p4.trans (Reaches.of_step (step_jmp h46 ?_)
      (Reaches.refl _ _))))) |>.state_eq (by omega)
    split_ifs <;> omega


/-! ### Tests -/

theorem Embedded.snap2 {μ : Machine} {s J y z : ℕ} (he : Embedded μ s (snap2 J y z s))
    (hy : y < J) (hz : z < J) (σ : ℕ → ℕ) (h0 : ∀ i, J ≤ i → σ i = 0) :
    Reaches μ ⟨s, σ⟩ ⟨s + 14, fun i => if i = aux J 2 then σ z else
      if i = aux J 0 then σ y else σ i⟩ := by
  obtain ⟨he1, he2⟩ := he.split
  have hJ := h0 J le_rfl
  have hA0 := h0 (aux J 0) (by aomega)
  have hA1 := h0 (aux J 1) (by aomega)
  have hA2 := h0 (aux J 2) (by aomega)
  refine Reaches.regs_eq (Reaches.state_eq ((he1.snap (by aomega) (by aomega) (by aomega)
    (by aomega) (by aomega) (by aomega) σ hJ hA0 hA1).trans'
      ((he2.shift (by simp)).snap (by aomega) (by aomega) (by aomega) (by aomega) (by aomega)
        (by aomega) _ ?_ ?_ ?_) (by omega)) (by omega)) ?_
  · simp only [aux] at *; split_ifs <;> omega
  · simp only [aux] at *; split_ifs <;> omega
  · simp only [aux] at *; split_ifs <;> omega
  · funext i; simp only [aux] at *
    split_ifs <;> subst_vars <;> omega

/-- The comparison loop of the test `y < z` on the copies `a`, `b`. -/
theorem reaches_ltLoop {μ : Machine} {u J a b th el : ℕ} (h0 : μ u = .dec b (u + 1) (u + 4))
    (h1 : μ (u + 1) = .dec a u (u + 2)) (h2 : μ (u + 2) = .dec b (u + 2) (u + 2 + 1))
    (h3 : μ (u + 3) = jmp J th) (h4 : μ (u + 4) = .dec a (u + 4) (u + 4 + 1))
    (h5 : μ (u + 5) = jmp J el) (hab : a ≠ b) (hJa : J ≠ a) (hJb : J ≠ b) (σ : ℕ → ℕ)
    (hJ : σ J = 0) :
    Reaches μ ⟨u, σ⟩ ⟨if σ a < σ b then th else el, fun i => if i = a then 0 else
      if i = b then 0 else σ i⟩ := by
  induction hn : σ b generalizing σ with
  | zero =>
    rw [ite_eq_right (by omega)]
    refine Reaches.of_step (step_dec_zero h0 hn) ((reaches_clear h4 σ).trans
      (Reaches.of_step (step_jmp h5 ?_) (Reaches.refl _ _))) |>.regs_eq ?_
    · simp [Function.update_apply, hJa, hJ]
    · funext i; simp [Function.update_apply]; split_ifs <;> subst_vars <;> omega
  | succ n ih =>
    have e1 := step_dec_pos h0 (σ := σ) (by omega)
    by_cases ha : σ a = 0
    · rw [ite_eq_left (by omega)]
      refine Reaches.of_step e1 (Reaches.of_step (step_dec_zero h1 (by simp [Function.update_apply, hab, ha]))
        ((reaches_clear h2 _).trans (Reaches.of_step (step_jmp (by simpa using h3) ?_)
          (Reaches.refl _ _)))) |>.regs_eq ?_
      · simp [Function.update_apply, hJa, hJb, hJ]
      · funext i; simp [Function.update_apply]; split_ifs <;> subst_vars <;> omega
    · have e2 := step_dec_pos h1 (σ := Function.update σ b (σ b - 1))
        (by simp [Function.update_apply, hab, ha])
      have := ih (Function.update (Function.update σ b (σ b - 1)) a
        (Function.update σ b (σ b - 1) a - 1)) (by simp [Function.update_apply, hJa, hJb, hJ])
        (by simp [Function.update_apply, hab.symm]; omega)
      have hc : (Function.update (Function.update σ b (σ b - 1)) a
          (Function.update σ b (σ b - 1) a - 1) a < n) = (σ a < n + 1) := by
        simp [Function.update_apply, hab, hab.symm]; omega
      simp only [hc] at this
      refine Reaches.of_step e1 (Reaches.of_step e2 this) |>.regs_eq ?_
      funext i; simp [Function.update_apply]; split_ifs <;> subst_vars <;> omega

/-- The comparison loop of the test `y = z` on the copies `a`, `b`. -/
theorem reaches_eqLoop {μ : Machine} {u J a b th el : ℕ} (h0 : μ u = .dec b (u + 1) (u + 2))
    (h1 : μ (u + 1) = .dec a u (u + 3)) (h2 : μ (u + 2) = .dec a (u + 5) (u + 7))
    (h3 : μ (u + 3) = .dec b (u + 3) (u + 3 + 1)) (h4 : μ (u + 4) = jmp J el)
    (h5 : μ (u + 5) = .dec a (u + 5) (u + 5 + 1)) (h6 : μ (u + 6) = jmp J el)
    (h7 : μ (u + 7) = jmp J th) (hab : a ≠ b) (hJa : J ≠ a) (hJb : J ≠ b) (σ : ℕ → ℕ)
    (hJ : σ J = 0) :
    Reaches μ ⟨u, σ⟩ ⟨if σ a = σ b then th else el, fun i => if i = a then 0 else
      if i = b then 0 else σ i⟩ := by
  induction hn : σ b generalizing σ with
  | zero =>
    by_cases ha : σ a = 0
    · rw [ite_eq_left (by omega)]
      refine Reaches.of_step (step_dec_zero h0 hn) (Reaches.of_step (step_dec_zero h2 ha)
        (Reaches.of_step (step_jmp h7 hJ) (Reaches.refl _ _))) |>.regs_eq ?_
      funext i; split_ifs <;> subst_vars <;> omega
    · rw [ite_eq_right (by omega)]
      refine Reaches.of_step (step_dec_zero h0 hn) (Reaches.of_step (step_dec_pos h2 ha)
        ((reaches_clear h5 _).trans (Reaches.of_step (step_jmp h6 ?_) (Reaches.refl _ _)))) |>.regs_eq ?_
      · simp [Function.update_apply, hJa, hJ]
      · funext i; simp [Function.update_apply]; split_ifs <;> subst_vars <;> omega
  | succ n ih =>
    have e1 := step_dec_pos h0 (σ := σ) (by omega)
    by_cases ha : σ a = 0
    · rw [ite_eq_right (by omega)]
      refine Reaches.of_step e1 (Reaches.of_step (step_dec_zero h1 (by simp [Function.update_apply, hab, ha]))
        ((reaches_clear h3 _).trans (Reaches.of_step (step_jmp h4 ?_)
          (Reaches.refl _ _)))) |>.regs_eq ?_
      · simp [Function.update_apply, hJa, hJb, hJ]
      · funext i; simp [Function.update_apply]; split_ifs <;> subst_vars <;> omega
    · have e2 := step_dec_pos h1 (σ := Function.update σ b (σ b - 1))
        (by simp [Function.update_apply, hab, ha])
      have := ih (Function.update (Function.update σ b (σ b - 1)) a
        (Function.update σ b (σ b - 1) a - 1)) (by simp [Function.update_apply, hJa, hJb, hJ])
        (by simp [Function.update_apply, hab.symm]; omega)
      have hc : (Function.update (Function.update σ b (σ b - 1)) a
          (Function.update σ b (σ b - 1) a - 1) a = n) = (σ a = n + 1) := by
        simp [Function.update_apply, hab, hab.symm]; omega
      simp only [hc] at this
      refine Reaches.of_step e1 (Reaches.of_step e2 this) |>.regs_eq ?_
      funext i; simp [Function.update_apply]; split_ifs <;> subst_vars <;> omega


theorem ltTest_reaches {μ : Machine} {s J y z th el : ℕ} (hy : y < J) (hz : z < J)
    (he : Embedded μ s (ltTest J y z s th el)) (σ : ℕ → ℕ) (h0 : ∀ i, J ≤ i → σ i = 0) :
    Reaches μ ⟨s, σ⟩ ⟨if σ y < σ z then th else el, σ⟩ := by
  obtain ⟨he1, he2⟩ := he.split
  have g : ∀ k (hk : k < 6), μ (s + 14 + k) = _ := fun k hk => he2 k (by simp; omega)
  have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega)
  have g3 := g 3 (by omega); have g4 := g 4 (by omega); have g5 := g 5 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, snap2_length, Nat.add_zero] at g0 g1 g2 g3 g4 g5
  have hJ := h0 J le_rfl
  have hA0 := h0 (aux J 0) (by aomega)
  have hA2 := h0 (aux J 2) (by aomega)
  have r := (he1.snap2 hy hz σ h0).trans (reaches_ltLoop (u := s + 14) (by simpa using g0)
    (by simpa using g1) (by simpa using g2) (by simpa using g3) (by simpa using g4)
    (by simpa using g5) (by aomega) (by aomega) (by aomega) _ (by simp only [aux] at *; split_ifs <;> omega))
  refine (r.state_eq (if_congr ?_ rfl rfl)).regs_eq ?_
  · simp only [aux] at *; split_ifs <;> omega
  · funext i; simp only [aux, Nat.add_zero] at *; split_ifs <;> subst_vars <;> omega

theorem eqTest_reaches {μ : Machine} {s J y z th el : ℕ} (hy : y < J) (hz : z < J)
    (he : Embedded μ s (eqTest J y z s th el)) (σ : ℕ → ℕ) (h0 : ∀ i, J ≤ i → σ i = 0) :
    Reaches μ ⟨s, σ⟩ ⟨if σ y = σ z then th else el, σ⟩ := by
  obtain ⟨he1, he2⟩ := he.split
  have g : ∀ k (hk : k < 8), μ (s + 14 + k) = _ := fun k hk => he2 k (by simp; omega)
  have g0 := g 0 (by omega); have g1 := g 1 (by omega); have g2 := g 2 (by omega)
  have g3 := g 3 (by omega); have g4 := g 4 (by omega); have g5 := g 5 (by omega)
  have g6 := g 6 (by omega); have g7 := g 7 (by omega)
  simp only [List.getElem_cons_zero, List.getElem_cons_succ, snap2_length, Nat.add_zero] at g0 g1 g2 g3 g4 g5 g6 g7
  have hJ := h0 J le_rfl
  have hA0 := h0 (aux J 0) (by aomega)
  have hA2 := h0 (aux J 2) (by aomega)
  have r := (he1.snap2 hy hz σ h0).trans (reaches_eqLoop (u := s + 14) (by simpa using g0)
    (by simpa using g1) (by simpa using g2) (by simpa using g3) (by simpa using g4)
    (by simpa using g5) (by simpa using g6) (by simpa using g7) (by aomega) (by aomega) (by aomega)
    _ (by simp only [aux] at *; split_ifs <;> omega))
  refine (r.state_eq (if_congr ?_ rfl rfl)).regs_eq ?_
  · simp only [aux] at *; split_ifs <;> omega
  · funext i; simp only [aux, Nat.add_zero] at *; split_ifs <;> subst_vars <;> omega

/-- **Block correctness**: every assignment block reaches its exit with `x` updated. -/
theorem assignB_reaches {μ : Machine} {s J x : ℕ} {o : Op} (hx : x < J) (ho : o.RegsBelow J)
    (he : Embedded μ s (assignB J x o s)) (σ : ℕ → ℕ) (h0 : ∀ i, J ≤ i → σ i = 0) :
    Reaches μ ⟨s, σ⟩ ⟨s + o.len, fun i => if i = x then o.eval σ else σ i⟩ := by
  cases o with
  | const k => exact assignB_const he σ
  | copy y => exact assignB_copy hx ho he σ h0
  | add y z => exact assignB_add hx ho.1 ho.2 he σ h0
  | sub y z => exact assignB_sub hx ho.1 ho.2 he σ h0
  | mul y z => exact assignB_mul hx ho.1 ho.2 he σ h0
  | div y z => exact (assignB_divMod true hx ho.1 ho.2 he σ h0).state_eq (by simp [Op.len])
  | mod y z => exact (assignB_divMod false hx ho.1 ho.2 he σ h0).state_eq (by simp [Op.len])

end ZInQ.Compiler.IR
