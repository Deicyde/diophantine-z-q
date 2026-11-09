import ZInQKernel.Compiler.Programs.Capped
import ZInQKernel.Compiler.Programs.FieldSpec

/-!
# Capped arithmetic routines (specifications)

Blueprint: `compiler/natural/programs/ir-capped-routines.md`.

All values are natural numbers held in integer variables; `Lv` holds the cap `L`. Each
routine computes the value prescribed by the mathematical definition (`saturate`,
`cappedMul`, `cappedPower`, `cappedFact`, the capped value of `e_A`, `cappedBound`,
`divFourLoop`) and writes only its result variable and the temporaries from its base.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace ZInQ.Compiler.IR

open Precision PrecisionArithmetic PrecisionAlgorithms

theorem saturate_mul_left' (L a b : ℕ) : saturate L (saturate L a * b) = saturate L (a * b) := by
  calc saturate L (saturate L a * b)
      = saturate L (saturate L (saturate L a) * saturate L b) := (saturate_mul L _ _).symm
    _ = saturate L (a * b) := by rw [saturate_saturate, saturate_mul]

theorem satCode_spec {Lv d x T : ℕ} (hd : d ≠ T ∧ d ≠ T + 1) (hx : x ≠ T ∧ x ≠ T + 1)
    (hL : Lv ≠ T ∧ Lv ≠ T + 1) {E : ℕ → ℤ} {L m : ℕ} (eL : (E Lv).natAbs = L)
    (ex : (E x).natAbs = m) :
    ∃ E', ZBigStep (satCode Lv d x T) E (.normal E') ∧ E' d = (saturate L m : ℕ) ∧
      ∀ v, v ≠ d → v ≠ T → v ≠ T + 1 → E' v = E v := by
  refine ⟨_, zbigStep_execZ (by simp [satCode, ZStmt.Plain]) E, ?_, fun v h1 h2 h3 => ?_⟩
  · simp only [satCode]; zexec_simp
    simp only [eL, ex, saturate, show Int.natAbs 1 = 1 from rfl, mul_one]; zcond_simp
    split_ifs <;> omega
  · simp only [satCode]; zexec_simp; zcond_simp; split_ifs <;> zexec_simp

theorem cmulCode_spec {Lv d a b T : ℕ} (hd : d ≠ T ∧ d ≠ T + 1 ∧ d ≠ T + 2)
    (ha : a ≠ T ∧ a ≠ T + 1 ∧ a ≠ T + 2) (hb : b ≠ T ∧ b ≠ T + 1 ∧ b ≠ T + 2)
    (hL : Lv ≠ T ∧ Lv ≠ T + 1 ∧ Lv ≠ T + 2) {E : ℕ → ℤ} {L m n : ℕ} (eL : (E Lv).natAbs = L)
    (ea : (E a).natAbs = m) (eb : (E b).natAbs = n) :
    ∃ E', ZBigStep (cmulCode Lv d a b T) E (.normal E') ∧ E' d = (cappedMul L m n : ℕ) ∧
      ∀ v, v ≠ d → v ≠ T → v ≠ T + 1 → v ≠ T + 2 → E' v = E v := by
  refine ⟨_, zbigStep_execZ (by simp [cmulCode, ZStmt.Plain]) E, ?_, fun v h1 h2 h3 h4 => ?_⟩
  · simp only [cmulCode]; zexec_simp; simp only [eL, ea, eb, cappedMul]; zcond_simp
    simp only [← Int.natCast_div, Int.natAbs_natCast, ← Nat.cast_mul]
    split_ifs <;> simp_all <;> omega
  · simp only [cmulCode]; zexec_simp; zcond_simp; split_ifs <;> zexec_simp


/-! ### Loops -/

theorem cpowLoop_spec {Lv x e T : ℕ} (hLv : Lv < T) (hx : x < T) (he : e < T) {L m n : ℕ} :
    ∀ k i (E : ℕ → ℤ), i + k = n → (E Lv).natAbs = L → (E x).natAbs = m → (E e).natAbs = n →
      E (T + 1) = i → E (T + 2) = 1 → E T = (saturate L (m ^ i) : ℕ) →
      ∃ E', ZBigStep (.loop (T + 1) e (cmulCode Lv T T x (T + 3) ;;;
          .assign (T + 1) (.nadd (T + 1) (T + 2)))) E (.normal E') ∧
        E' T = (saturate L (m ^ n) : ℕ) ∧ ∀ v < T, E' v = E v
  | 0, i, E, hik, eL, ex, ee, ei, e1, eT => by
    obtain rfl : i = n := by omega
    exact ⟨E, ZBigStep.loopFalse (by rw [ei, ee]; simp), eT, fun _ _ => rfl⟩
  | k + 1, i, E, hik, eL, ex, ee, ei, e1, eT => by
    obtain ⟨E₁, h₁, v₁, f₁⟩ := cmulCode_spec (Lv := Lv) (d := T) (a := T) (b := x) (T := T + 3)
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩
      ⟨by omega, by omega, by omega⟩ eL (by rw [eT, Int.natAbs_natCast]) ex
    set E₂ := Function.update E₁ (T + 1) (ZOp.eval E₁ (.nadd (T + 1) (T + 2))) with hE₂
    have g : ∀ v, v ≠ T → v ≠ T + 1 → v < T + 3 → E₂ v = E v := fun v h1 h2 h3 => by
      rw [hE₂, Function.update_of_ne h2, f₁ v h1 (by omega) (by omega) (by omega)]
    obtain ⟨E', h', v', f'⟩ := cpowLoop_spec (L := L) (m := m) (n := n) hLv hx he k (i + 1) E₂ (by omega)
      (by rw [g Lv (by omega) (by omega) (by omega), eL])
      (by rw [g x (by omega) (by omega) (by omega), ex])
      (by rw [g e (by omega) (by omega) (by omega), ee])
      (by simp [hE₂, ZOp.eval, f₁ (T + 1) (by omega) (by omega) (by omega) (by omega), ei,
        f₁ (T + 2) (by omega) (by omega) (by omega) (by omega), e1])
      (by rw [g (T + 2) (by omega) (by omega) (by omega), e1])
      (by rw [hE₂, Function.update_of_ne (by omega), v₁, cappedMul_eq_saturate,
        saturate_mul_left', pow_succ])
    have hc : (E (T + 1)).natAbs < (E e).natAbs := by rw [ei, ee]; simp; omega
    refine ⟨E', ZBigStep.loopNormal hc
      (ZBigStep.seqNormal h₁ (ZBigStep.assign _ _ _)) h', v', fun v hv => ?_⟩
    rw [f' v hv, g v (by omega) (by omega) (by omega)]

theorem cpowCode_spec {Lv d x e T : ℕ} (hLv : Lv < T) (hx : x < T) (he : e < T) (hd : d < T)
    {E : ℕ → ℤ} {L m n : ℕ} (eL : (E Lv).natAbs = L) (ex : (E x).natAbs = m)
    (ee : (E e).natAbs = n) :
    ∃ E', ZBigStep (cpowCode Lv d x e T) E (.normal E') ∧ E' d = (cappedPower L m n : ℕ) ∧
      ∀ v < T, v ≠ d → E' v = E v := by
  set E₃ := Function.update (Function.update (Function.update E T (ZOp.eval E (.const 1))) (T + 1)
    (ZOp.eval (Function.update E T (ZOp.eval E (.const 1))) (.const 0))) (T + 2)
    (ZOp.eval (Function.update (Function.update E T (ZOp.eval E (.const 1))) (T + 1)
    (ZOp.eval (Function.update E T (ZOp.eval E (.const 1))) (.const 0))) (.const 1)) with hE₃
  have g : ∀ v < T, E₃ v = E v := fun v hv => by
    rw [hE₃, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  obtain ⟨E', h', v', f'⟩ := cpowLoop_spec (L := L) (m := m) (n := n) hLv hx he n 0 E₃ (by omega) (by rw [g _ hLv, eL])
    (by rw [g _ hx, ex]) (by rw [g _ he, ee]) (by simp [hE₃, ZOp.eval])
    (by simp [hE₃, ZOp.eval]) (by simp [hE₃, ZOp.eval, saturate_one])
  refine ⟨_, ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.seqNormal (ZBigStep.assign _ _ _)
    (ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.seqNormal h' (ZBigStep.assign _ _ _)))),
    ?_, fun v hv hvd => ?_⟩
  · simp [ZOp.eval, v', cappedPower_eq_saturate]
  · rw [Function.update_of_ne hvd, f' v hv, g v hv]

theorem cfactLoop_spec {Lv n T : ℕ} (hLv : Lv < T) (hn : n < T) {L c : ℕ} :
    ∀ k i (E : ℕ → ℤ), i + k = c → (E Lv).natAbs = L → (E n).natAbs = c → E (T + 1) = i →
      E (T + 2) = 1 → E T = (cappedFact L i : ℕ) →
      ∃ E', ZBigStep (.loop (T + 1) n (.assign (T + 1) (.nadd (T + 1) (T + 2)) ;;;
          satCode Lv (T + 3) (T + 1) (T + 4) ;;; cmulCode Lv T T (T + 3) (T + 4))) E (.normal E') ∧
        E' T = (cappedFact L c : ℕ) ∧ ∀ v < T, E' v = E v
  | 0, i, E, hik, eL, en, ei, e1, eT => by
    obtain rfl : i = c := by omega
    exact ⟨E, ZBigStep.loopFalse (by rw [ei, en]; simp), eT, fun _ _ => rfl⟩
  | k + 1, i, E, hik, eL, en, ei, e1, eT => by
    set E₁ := Function.update E (T + 1) (ZOp.eval E (.nadd (T + 1) (T + 2))) with hE₁
    have g₁ : ∀ v, v ≠ T + 1 → E₁ v = E v := fun v hv => Function.update_of_ne hv _ _
    have e1i : E₁ (T + 1) = ((i + 1 : ℕ) : ℤ) := by simp [hE₁, ZOp.eval, ei, e1]
    obtain ⟨E₂, h₂, v₂, f₂⟩ := satCode_spec (E := E₁) (Lv := Lv) (d := T + 3) (x := T + 1) (T := T + 4)
      ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (by rw [g₁ Lv (by omega), eL]) (by rw [e1i, Int.natAbs_natCast])
    obtain ⟨E₃, h₃, v₃, f₃⟩ := cmulCode_spec (E := E₂) (Lv := Lv) (d := T) (a := T) (b := T + 3)
      (T := T + 4)
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩
      ⟨by omega, by omega, by omega⟩
      (by rw [f₂ Lv (by omega) (by omega) (by omega), g₁ Lv (by omega), eL])
      (by rw [f₂ T (by omega) (by omega) (by omega), g₁ T (by omega), eT, Int.natAbs_natCast])
      (by rw [v₂, Int.natAbs_natCast])
    have g : ∀ v, v ≠ T → v ≠ T + 1 → v ≠ T + 3 → v < T + 4 → E₃ v = E v := fun v h1 h2 h3 h4 => by
      rw [f₃ v h1 (by omega) (by omega) (by omega), f₂ v h3 (by omega) (by omega), g₁ v h2]
    obtain ⟨E', h', v', f'⟩ := cfactLoop_spec (L := L) (c := c) hLv hn k (i + 1) E₃ (by omega)
      (by rw [g Lv (by omega) (by omega) (by omega) (by omega), eL])
      (by rw [g n (by omega) (by omega) (by omega) (by omega), en])
      (by rw [f₃ _ (by omega) (by omega) (by omega) (by omega), f₂ _ (by omega) (by omega) (by omega), e1i])
      (by rw [g (T + 2) (by omega) (by omega) (by omega) (by omega), e1])
      (by rw [v₃, cappedFact])
    have hc : (E (T + 1)).natAbs < (E n).natAbs := by rw [ei, en]; simp; omega
    refine ⟨E', ZBigStep.loopNormal hc
      (ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.seqNormal h₂ h₃)) h', v', fun v hv => ?_⟩
    rw [f' v hv, g v (by omega) (by omega) (by omega) (by omega)]

theorem cfactCode_spec {Lv d n T : ℕ} (hLv : Lv < T) (hn : n < T) (hd : d < T)
    {E : ℕ → ℤ} {L c : ℕ} (eL : (E Lv).natAbs = L) (en : (E n).natAbs = c) :
    ∃ E', ZBigStep (cfactCode Lv d n T) E (.normal E') ∧ E' d = (cappedFact L c : ℕ) ∧
      ∀ v < T, v ≠ d → E' v = E v := by
  set E₃ := Function.update (Function.update (Function.update E T (ZOp.eval E (.const 1))) (T + 1)
    (ZOp.eval (Function.update E T (ZOp.eval E (.const 1))) (.const 0))) (T + 2)
    (ZOp.eval (Function.update (Function.update E T (ZOp.eval E (.const 1))) (T + 1)
    (ZOp.eval (Function.update E T (ZOp.eval E (.const 1))) (.const 0))) (.const 1)) with hE₃
  have g : ∀ v < T, E₃ v = E v := fun v hv => by
    rw [hE₃, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  obtain ⟨E', h', v', f'⟩ := cfactLoop_spec (L := L) (c := c) hLv hn c 0 E₃ (by omega) (by rw [g _ hLv, eL])
    (by rw [g _ hn, en]) (by simp [hE₃, ZOp.eval]) (by simp [hE₃, ZOp.eval])
    (by simp [hE₃, ZOp.eval, cappedFact])
  refine ⟨_, ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.seqNormal (ZBigStep.assign _ _ _)
    (ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.seqNormal h' (ZBigStep.assign _ _ _)))),
    ?_, fun v hv hvd => ?_⟩
  · simp [ZOp.eval, v']
  · rw [Function.update_of_ne hvd, f' v hv, g v hv]

theorem divFourLoop_spec {x β T : ℕ} (hx : x < T) (hβ : β < T) (hxβ : x ≠ β) {X B : ℕ} :
    ∀ k i (E : ℕ → ℤ), i + k = B → (E β).natAbs = B → E T = i → E (T + 1) = 1 → E (T + 2) = 4 →
      E x = (X / 4 ^ i : ℕ) →
      ∃ E', ZBigStep (.loop T β (.assign x (.div x (T + 2)) ;;; .assign T (.nadd T (T + 1)))) E
          (.normal E') ∧ E' x = (divFourLoop X B : ℕ) ∧ ∀ v < T, v ≠ x → E' v = E v
  | 0, i, E, hik, eβ, ei, e1, e4, ex => by
    obtain rfl : i = B := by omega
    refine ⟨E, ZBigStep.loopFalse (by rw [ei, eβ]; simp), ?_, fun _ _ _ => rfl⟩
    rw [ex, divFourLoop_eq]
  | k + 1, i, E, hik, eβ, ei, e1, e4, ex => by
    set E₁ := Function.update E x (ZOp.eval E (.div x (T + 2))) with hE₁
    set E₂ := Function.update E₁ T (ZOp.eval E₁ (.nadd T (T + 1))) with hE₂
    have g : ∀ v, v ≠ x → v ≠ T → E₂ v = E v := fun v h1 h2 => by
      rw [hE₂, Function.update_of_ne h2, hE₁, Function.update_of_ne h1]
    have ex1 : E₁ x = ((X / 4 ^ (i + 1) : ℕ) : ℤ) := by
      rw [hE₁, Function.update_self]
      simp only [ZOp.eval, ex, Int.natAbs_natCast, e4, show Int.natAbs 4 = 4 from rfl,
        Nat.div_div_eq_div_mul, pow_succ]
    have ex2 : E₂ x = ((X / 4 ^ (i + 1) : ℕ) : ℤ) := by
      rw [hE₂, Function.update_of_ne (by omega), ex1]
    have eT2 : E₂ T = ((i + 1 : ℕ) : ℤ) := by
      rw [hE₂, Function.update_self]
      simp only [ZOp.eval, hE₁, Function.update_of_ne (show T ≠ x by omega),
        Function.update_of_ne (show T + 1 ≠ x by omega), ei, e1, Int.natAbs_natCast,
        show Int.natAbs 1 = 1 from rfl]
    obtain ⟨E', h', v', f'⟩ := divFourLoop_spec (X := X) (B := B) hx hβ hxβ k (i + 1) E₂ (by omega)
      (by rw [g β (by omega) (by omega), eβ]) eT2
      (by rw [g (T + 1) (by omega) (by omega), e1]) (by rw [g (T + 2) (by omega) (by omega), e4])
      ex2
    have hc : (E T).natAbs < (E β).natAbs := by rw [ei, eβ]; simp; omega
    refine ⟨E', ZBigStep.loopNormal hc
      (ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.assign _ _ _)) h', v',
      fun v hv hvx => ?_⟩
    rw [f' v hv hvx, g v hvx (by omega)]

theorem divFourCode_spec {x β T : ℕ} (hx : x < T) (hβ : β < T) (hxβ : x ≠ β) {E : ℕ → ℤ} {X B : ℕ}
    (ex : E x = X) (eβ : (E β).natAbs = B) :
    ∃ E', ZBigStep (divFourCode x β T) E (.normal E') ∧ E' x = (divFourLoop X B : ℕ) ∧
      ∀ v < T, v ≠ x → E' v = E v := by
  set E₃ := Function.update (Function.update (Function.update E T (ZOp.eval E (.const 0))) (T + 1)
    (ZOp.eval (Function.update E T (ZOp.eval E (.const 0))) (.const 1))) (T + 2)
    (ZOp.eval (Function.update (Function.update E T (ZOp.eval E (.const 0))) (T + 1)
    (ZOp.eval (Function.update E T (ZOp.eval E (.const 0))) (.const 1))) (.const 4)) with hE₃
  have g : ∀ v < T, E₃ v = E v := fun v hv => by
    rw [hE₃, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]
  obtain ⟨E', h', v', f'⟩ := divFourLoop_spec (X := X) (B := B) hx hβ hxβ B 0 E₃ (by omega) (by rw [g _ hβ, eβ])
    (by simp [hE₃, ZOp.eval]) (by simp [hE₃, ZOp.eval]) (by simp [hE₃, ZOp.eval])
    (by rw [g _ hx, ex]; simp)
  refine ⟨E', ZBigStep.seqNormal (ZBigStep.assign _ _ _) (ZBigStep.seqNormal (ZBigStep.assign _ _ _)
    (ZBigStep.seqNormal (ZBigStep.assign _ _ _) h')), v', fun v hv hvx => ?_⟩
  rw [f' v hv hvx, g v hv]


/-! ### Literals, sums and maxima -/

theorem satLit_spec {Lv d c T : ℕ} (hd : d ≠ T ∧ d ≠ T + 1 ∧ d ≠ T + 2)
    (hL : Lv ≠ T ∧ Lv ≠ T + 1 ∧ Lv ≠ T + 2) {E : ℕ → ℤ} {L : ℕ} (eL : (E Lv).natAbs = L) :
    ∃ E', ZBigStep (satLit Lv d c T) E (.normal E') ∧ E' d = (saturate L c : ℕ) ∧
      ∀ v, v ≠ d → v ≠ T → v ≠ T + 1 → v ≠ T + 2 → E' v = E v := by
  obtain ⟨E₁, h₁, v₁, f₁⟩ := natConst_spec T c (T + 1) (by omega) E
  obtain ⟨E₂, h₂, v₂, f₂⟩ := satCode_spec (E := E₁) (Lv := Lv) (d := d) (x := T) (T := T + 1)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (by rw [f₁ Lv (by omega) (by omega), eL]) (by rw [v₁, Int.natAbs_natCast])
  refine ⟨E₂, ZBigStep.seqNormal h₁ h₂, v₂, fun v h1 h2 h3 h4 => ?_⟩
  rw [f₂ v h1 h3 h4, f₁ v h2 h3]

theorem caddCode_spec {Lv d a b T : ℕ} (hd : d ≠ T ∧ d ≠ T + 1 ∧ d ≠ T + 2)
    (hL : Lv ≠ T ∧ Lv ≠ T + 1 ∧ Lv ≠ T + 2) {E : ℕ → ℤ} {L m n : ℕ} (eL : (E Lv).natAbs = L)
    (ea : (E a).natAbs = m) (eb : (E b).natAbs = n) :
    ∃ E', ZBigStep (caddCode Lv d a b T) E (.normal E') ∧ E' d = (saturate L (m + n) : ℕ) ∧
      ∀ v, v ≠ d → v ≠ T → v ≠ T + 1 → v ≠ T + 2 → E' v = E v := by
  obtain ⟨E₂, h₂, v₂, f₂⟩ := satCode_spec (E := Function.update E T (ZOp.eval E (.nadd a b)))
    (Lv := Lv) (d := d) (x := T) (T := T + 1) (m := m + n) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩ (by rw [Function.update_of_ne (by omega), eL])
    (by simp [ZOp.eval, ea, eb]; omega)
  refine ⟨E₂, ZBigStep.seqNormal (ZBigStep.assign _ _ _) h₂, v₂, fun v h1 h2 h3 h4 => ?_⟩
  rw [f₂ v h1 h3 h4, Function.update_of_ne h2]

theorem cmaxCode_spec {Lv d a b T : ℕ} (hd : d ≠ T ∧ d ≠ T + 1 ∧ d ≠ T + 2)
    (hL : Lv ≠ T ∧ Lv ≠ T + 1 ∧ Lv ≠ T + 2) {E : ℕ → ℤ} {L m n : ℕ} (eL : (E Lv).natAbs = L)
    (ea : (E a).natAbs = m) (eb : (E b).natAbs = n) :
    ∃ E', ZBigStep (cmaxCode Lv d a b T) E (.normal E') ∧ E' d = (saturate L (max m n) : ℕ) ∧
      ∀ v, v ≠ d → v ≠ T → v ≠ T + 1 → v ≠ T + 2 → E' v = E v := by
  obtain ⟨E₁, h₁, v₁, f₁⟩ : ∃ E₁, ZBigStep (.ite (.nlt a b) (.assign T (.copy b))
      (.assign T (.copy a))) E (.normal E₁) ∧ (E₁ T).natAbs = max m n ∧ ∀ v, v ≠ T → E₁ v = E v := by
    by_cases hab : m < n
    · exact ⟨_, ZBigStep.iteTrue (by simp [ZCond.Holds, ea, eb, hab]) (ZBigStep.assign _ _ _),
        by simp [ZOp.eval, eb]; omega, fun v hv => Function.update_of_ne hv _ _⟩
    · exact ⟨_, ZBigStep.iteFalse (by simp [ZCond.Holds, ea, eb, hab]) (ZBigStep.assign _ _ _),
        by simp [ZOp.eval, ea]; omega, fun v hv => Function.update_of_ne hv _ _⟩
  obtain ⟨E₂, h₂, v₂, f₂⟩ := satCode_spec (E := E₁) (Lv := Lv) (d := d) (x := T) (T := T + 1)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (by rw [f₁ Lv (by omega), eL]) v₁
  refine ⟨E₂, ZBigStep.seqNormal h₁ h₂, v₂, fun v h1 h2 h3 h4 => ?_⟩
  rw [f₂ v h1 h3 h4, f₁ v h2]


/-! ### Straight-line capped programs and the precision height constant -/

/-- A capped operation on slots. -/
inductive COp
  | lit (c : ℕ)
  | add (a b : ℕ)
  | mul (a b : ℕ)
  | max (a b : ℕ)
  | pow (a b : ℕ)
  | fact (a : ℕ)

/-- The routine of a capped operation, writing `d`, temporaries from `W`. -/
def COp.code (Lv d W : ℕ) : COp → ZStmt
  | .lit c => satLit Lv d c W
  | .add a b => caddCode Lv d a b W
  | .mul a b => cmulCode Lv d a b W
  | .max a b => cmaxCode Lv d a b W
  | .pow a b => cpowCode Lv d a b W
  | .fact a => cfactCode Lv d a W

/-- The value of a capped operation on natural slot values `S`. -/
def COp.eval (L : ℕ) (S : ℕ → ℕ) : COp → ℕ
  | .lit c => saturate L c
  | .add a b => saturate L (S a + S b)
  | .mul a b => cappedMul L (S a) (S b)
  | .max a b => saturate L (Max.max (S a) (S b))
  | .pow a b => cappedPower L (S a) (S b)
  | .fact a => cappedFact L (S a)

/-- The operands of a capped operation are below `W`. -/
def COp.ReadsBelow (W : ℕ) : COp → Prop
  | .lit _ => True
  | .add a b | .mul a b | .max a b | .pow a b => a < W ∧ b < W
  | .fact a => a < W

theorem COp.eval_congr {L W : ℕ} {S S' : ℕ → ℕ} (h : ∀ v < W, S' v = S v) {op : COp}
    (hop : op.ReadsBelow W) : op.eval L S' = op.eval L S := by
  cases op with
  | lit c => rfl
  | add a b | mul a b | max a b | pow a b => simp [COp.eval, h a hop.1, h b hop.2]
  | fact a => simp [COp.eval, h a hop]

theorem COp.code_spec {Lv d W : ℕ} {op : COp} (hd : d < W) (hLv : Lv < W)
    (hop : op.ReadsBelow W) {E : ℕ → ℤ} {L : ℕ} (eL : (E Lv).natAbs = L) :
    ∃ E', ZBigStep (op.code Lv d W) E (.normal E') ∧
      E' d = (op.eval L (fun v => (E v).natAbs) : ℕ) ∧ ∀ v < W, v ≠ d → E' v = E v := by
  cases op with
  | lit c =>
    obtain ⟨E', h, v, f⟩ := satLit_spec (c := c) (d := d) (T := W) ⟨by omega, by omega, by omega⟩
      ⟨by omega, by omega, by omega⟩ eL
    exact ⟨E', h, v, fun u hu h1 => f u h1 (by omega) (by omega) (by omega)⟩
  | add a b =>
    obtain ⟨E', h, v, f⟩ := caddCode_spec (a := a) (b := b) (d := d) (T := W)
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ eL rfl rfl
    exact ⟨E', h, v, fun u hu h1 => f u h1 (by omega) (by omega) (by omega)⟩
  | mul a b =>
    obtain ⟨E', h, v, f⟩ := cmulCode_spec (a := a) (b := b) (d := d) (T := W)
      ⟨by omega, by omega, by omega⟩ ⟨by have := hop.1; omega, by have := hop.1; omega,
        by have := hop.1; omega⟩ ⟨by have := hop.2; omega, by have := hop.2; omega,
        by have := hop.2; omega⟩ ⟨by omega, by omega, by omega⟩ eL rfl rfl
    exact ⟨E', h, v, fun u hu h1 => f u h1 (by omega) (by omega) (by omega)⟩
  | max a b =>
    obtain ⟨E', h, v, f⟩ := cmaxCode_spec (a := a) (b := b) (d := d) (T := W)
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩ eL rfl rfl
    exact ⟨E', h, v, fun u hu h1 => f u h1 (by omega) (by omega) (by omega)⟩
  | pow a b =>
    exact cpowCode_spec hLv hop.1 hop.2 hd eL rfl rfl
  | fact a =>
    exact cfactCode_spec hLv hop hd eL rfl

/-- Straight-line capped operations followed by a continuation. -/
def CProg.code (Lv W : ℕ) : List (ℕ × COp) → ZStmt → ZStmt
  | [], c => c
  | (d, op) :: l, c => op.code Lv d W ;;; CProg.code Lv W l c

/-- The functional semantics. -/
def CProg.sem (L : ℕ) : List (ℕ × COp) → (ℕ → ℤ) → (ℕ → ℤ)
  | [], E => E
  | (d, op) :: l, E =>
    CProg.sem L l (Function.update E d (op.eval L (fun v => (E v).natAbs) : ℕ))

/-- Destinations below `W` and different from `Lv`, operands below `W`. -/
def CProg.WF (Lv W : ℕ) (l : List (ℕ × COp)) : Prop :=
  ∀ dop ∈ l, dop.1 < W ∧ dop.1 ≠ Lv ∧ dop.2.ReadsBelow W

theorem CProg.sem_congr {L W : ℕ} : ∀ {l : List (ℕ × COp)}, (∀ dop ∈ l, dop.1 < W ∧
    dop.2.ReadsBelow W) → ∀ {E₁ E₂ : ℕ → ℤ}, (∀ v < W, E₁ v = E₂ v) →
    ∀ v < W, CProg.sem L l E₁ v = CProg.sem L l E₂ v
  | [], _, _, _, h => h
  | (d, op) :: l, hl, E₁, E₂, h => by
    refine CProg.sem_congr (l := l) (fun dop hdop => hl dop (List.mem_cons_of_mem _ hdop)) ?_
    intro v hv
    have hop := (hl (d, op) (by simp)).2
    have he : op.eval L (fun v => (E₁ v).natAbs) = op.eval L (fun v => (E₂ v).natAbs) :=
      COp.eval_congr (fun v hv => by simp [h v hv]) hop
    simp only [Function.update_apply, he]
    split_ifs <;> simp [h v hv]

theorem CProg.code_spec {Lv W L : ℕ} (hLv : Lv < W) : ∀ (l : List (ℕ × COp)),
    CProg.WF Lv W l → ∀ E : ℕ → ℤ, (E Lv).natAbs = L →
    ∃ E', (∀ v < W, E' v = CProg.sem L l E v) ∧
      ∀ c o, ZBigStep c E' o → ZBigStep (CProg.code Lv W l c) E o
  | [], _, E, _ => ⟨E, fun _ _ => rfl, fun _ _ h => h⟩
  | (d, op) :: l, hl, E, eL => by
    obtain ⟨hd, hdL, hop⟩ := hl (d, op) (by simp)
    have hl' : CProg.WF Lv W l := fun dop hdop => hl dop (List.mem_cons_of_mem _ hdop)
    obtain ⟨E₁, h₁, v₁, f₁⟩ := COp.code_spec (op := op) hd hLv hop eL
    obtain ⟨E₂, a₂, c₂⟩ := CProg.code_spec hLv l hl' E₁ (by rw [f₁ Lv hLv (Ne.symm hdL), eL])
    refine ⟨E₂, fun v hv => ?_, fun c o h => ZBigStep.seqNormal h₁ (c₂ c o h)⟩
    rw [a₂ v hv]
    refine CProg.sem_congr (fun dop hdop => ⟨(hl' dop hdop).1, (hl' dop hdop).2.2⟩)
      (fun u hu => ?_) v hv
    simp only [Function.update_apply]
    split_ifs with h1
    · subst h1; exact v₁
    · exact f₁ u hu h1


/-- The straight-line capped program of `⟨e_A⟩_L` (slots `V, …, V + 39`). -/
def cA0List (V : ℕ) : List (ℕ × COp) :=
  [(V, .lit 324), (V + 1, .fact V), (V + 2, .lit 4), (V + 3, .pow (V + 1) (V + 2)),
   (V + 4, .lit 256), (V + 5, .mul (V + 4) (V + 3)), (V + 6, .lit 3),
   (V + 7, .pow (V + 6) (V + 5)), (V + 8, .mul (V + 1) (V + 7)),
   (V + 9, .lit 116064000000), (V + 10, .mul (V + 8) (V + 9)), (V + 11, .lit 2),
   (V + 12, .pow (V + 10) (V + 11)), (V + 13, .lit 10), (V + 14, .mul (V + 13) (V + 12)),
   (V + 15, .mul (V + 8) (V + 14)), (V + 16, .pow (V + 8) (V + 15)),
   (V + 17, .pow (V + 8) (V + 11)), (V + 18, .lit 21000), (V + 19, .mul (V + 18) (V + 17)),
   (V + 20, .pow (V + 6) (V + 19)), (V + 21, .mul (V + 17) (V + 20)), (V + 22, .lit 1),
   (V + 23, .add (V + 21) (V + 22)), (V + 24, .mul (V + 11) (V + 23)), (V + 25, .lit 1028),
   (V + 26, .lit 5), (V + 27, .mul (V + 26) (V + 8)), (V + 28, .add (V + 25) (V + 27)),
   (V + 29, .lit 84000), (V + 30, .mul (V + 29) (V + 17)), (V + 31, .add (V + 28) (V + 30)),
   (V + 32, .lit 4096), (V + 33, .mul (V + 32) (V + 31)), (V + 34, .add (V + 24) (V + 33)),
   (V + 35, .lit 10000000000000), (V + 36, .mul (V + 11) (V + 35)), (V + 37, .lit 17),
   (V + 38, .pow (V + 16) (V + 37)), (V + 39, .max (V + 34) (V + 38)),
   (V + 39, .max (V + 22) (V + 39))]

theorem CProg.sem_frame {L V : ℕ} : ∀ {l : List (ℕ × COp)}, (∀ dop ∈ l, V ≤ dop.1) →
    ∀ (E : ℕ → ℤ) v, v < V → CProg.sem L l E v = E v
  | [], _, _, _, _ => rfl
  | (d, op) :: l, hl, E, v, hv => by
    rw [CProg.sem, CProg.sem_frame (fun dop hdop => hl dop (List.mem_cons_of_mem _ hdop)) _ v hv]
    have := hl (d, op) (by simp)
    exact Function.update_of_ne (by simp at this; omega) _ _

theorem cA0Code_eq (Lv d V : ℕ) :
    cA0Code Lv d V = CProg.code Lv (V + 40) (cA0List V) (cmulCode Lv d (V + 36) (V + 39) (V + 40)) :=
  rfl

theorem cA0Code_spec {Lv d V : ℕ} (hLv : Lv < V) (hd : d < V) {E : ℕ → ℤ} {L : ℕ}
    (eL : (E Lv).natAbs = L) :
    ∃ E', ZBigStep (cA0Code Lv d V) E (.normal E') ∧ E' d = (NExpr.eA.capped L : ℕ) ∧
      ∀ v < V, v ≠ d → E' v = E v := by
  have wf : CProg.WF Lv (V + 40) (cA0List V) := by
    intro dop hdop
    simp only [cA0List, List.mem_cons, List.mem_nil_iff, or_false] at hdop
    rcases hdop with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h <;> simp [COp.ReadsBelow] <;> omega
  obtain ⟨E₁, a₁, c₁⟩ := CProg.code_spec (L := L) (by omega) (cA0List V) wf E eL
  have hsem : ∀ v < V, CProg.sem L (cA0List V) E v = E v := by
    refine CProg.sem_frame (fun dop hdop => ?_) E
    simp only [cA0List, List.mem_cons, List.mem_nil_iff, or_false] at hdop
    rcases hdop with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h <;> simp
  obtain ⟨E₂, h₂, v₂, f₂⟩ := cmulCode_spec (E := E₁) (Lv := Lv) (d := d) (a := V + 36)
    (b := V + 39) (T := V + 40) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩
    ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩
    (by rw [a₁ Lv (by omega), hsem Lv hLv, eL]) rfl rfl
  refine ⟨E₂, by rw [cA0Code_eq]; exact c₁ _ _ h₂, ?_, fun v hv hvd => ?_⟩
  · rw [v₂, a₁ _ (by omega), a₁ _ (by omega)]
    simp only [cA0List, CProg.sem, COp.eval, Function.update_apply, Int.natAbs_natCast,
      Nat.reduceEqDiff, Nat.left_eq_add, Nat.add_left_cancel_iff, OfNat.ofNat_ne_zero,
      ↓reduceIte]
    simp only [NExpr.eA, NExpr.eC, NExpr.eB, NExpr.eQ0, NExpr.eE0, NExpr.eG0, NExpr.eD,
      NExpr.eF0, NExpr.capped]
  · rw [f₂ v hvd (by omega) (by omega) (by omega), a₁ v (by omega), hsem v hv]


theorem cBoundCode_spec {Lv d M V : ℕ} (hLv : Lv < V) (hd : d < V) (hM : M < V) {E : ℕ → ℤ}
    {L m : ℕ} (eL : (E Lv).natAbs = L) (eM : (E M).natAbs = m) :
    ∃ E', ZBigStep (cBoundCode Lv d M V) E (.normal E') ∧ E' d = (cappedBound L m : ℕ) ∧
      ∀ v < V, v ≠ d → E' v = E v := by
  obtain ⟨E₁, h₁, v₁, f₁⟩ := cA0Code_spec (Lv := Lv) (d := V) (V := V + 4) (by omega) (by omega) eL
  obtain ⟨E₂, h₂, v₂, f₂⟩ := satCode_spec (E := E₁) (Lv := Lv) (d := V + 1) (x := M) (T := V + 4)
    ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
    (by rw [f₁ Lv (by omega) (by omega), eL]) (by rw [f₁ M (by omega) (by omega), eM])
  obtain ⟨E₃, h₃, v₃, f₃⟩ := natConst_spec (V + 2) 24 (V + 4) (by omega) E₂
  obtain ⟨E₄, h₄, v₄, f₄⟩ := cpowCode_spec (E := E₃) (Lv := Lv) (d := V + 3) (x := V + 1)
    (e := V + 2) (T := V + 4) (by omega) (by omega) (by omega) (by omega)
    (by rw [f₃ Lv (by omega) (by omega), f₂ Lv (by omega) (by omega) (by omega),
      f₁ Lv (by omega) (by omega), eL])
    (by rw [f₃ (V + 1) (by omega) (by omega), v₂, Int.natAbs_natCast])
    (n := 24) (by rw [v₃]; rfl)
  obtain ⟨E₅, h₅, v₅, f₅⟩ := cmulCode_spec (E := E₄) (Lv := Lv) (d := d) (a := V) (b := V + 3)
    (T := V + 4) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩
    ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩
    (by rw [f₄ Lv (by omega) (by omega), f₃ Lv (by omega) (by omega),
      f₂ Lv (by omega) (by omega) (by omega), f₁ Lv (by omega) (by omega), eL])
    (by rw [f₄ V (by omega) (by omega), f₃ V (by omega) (by omega),
      f₂ V (by omega) (by omega) (by omega), v₁, Int.natAbs_natCast])
    (by rw [v₄, Int.natAbs_natCast])
  refine ⟨E₅, ZBigStep.seqNormal h₁ (ZBigStep.seqNormal h₂ (ZBigStep.seqNormal h₃
    (ZBigStep.seqNormal h₄ h₅))), by rw [v₅, cappedBound], fun v hv hvd => ?_⟩
  rw [f₅ v hvd (by omega) (by omega) (by omega), f₄ v (by omega) (by omega),
    f₃ v (by omega) (by omega), f₂ v (by omega) (by omega) (by omega), f₁ v (by omega) (by omega)]

end ZInQ.Compiler.IR
