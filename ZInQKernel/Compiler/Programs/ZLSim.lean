import ZInQKernel.Compiler.Programs.ZL
import ZInQKernel.Compiler.Programs.SignedSpec

/-!
# The integer layer simulates its semantics

`ReprEnv off K ρ E`: the register pairs of the integer variables `k < K` represent `E k`. If
`⟨S, E⟩ ⇓ o` over integer environments, the compiled statement (temporaries from
`t ≥ off + 2K`) has the corresponding outcome from any file representing `E`
(`ZStmt.compile_sim`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace ZInQ.Compiler.IR

/-- The register pairs of the variables below `K` represent the environment `E`. -/
def ReprEnv (off K : ℕ) (ρ : ℕ → ℕ) (E : ℕ → ℤ) : Prop :=
  ∀ k < K, ReprInt ρ (zvar off k) (E k)

theorem zvar_below {off K k t : ℕ} (hk : k < K) (ht : off + 2 * K ≤ t) : (zvar off k).Below t :=
  ⟨by simp [zvar]; omega, by simp [zvar]; omega⟩

theorem zvar_ne (off k : ℕ) : (zvar off k).sign ≠ (zvar off k).mag := by simp [zvar]

theorem ReprEnv.update {off K t k : ℕ} {ρ ρ' : ℕ → ℕ} {E : ℕ → ℤ} {v : ℤ}
    (h : ReprEnv off K ρ E) (ht : off + 2 * K ≤ t) (hr : ReprInt ρ' (zvar off k) v)
    (hf : ∀ i < t, i ≠ (zvar off k).sign → i ≠ (zvar off k).mag → ρ' i = ρ i) :
    ReprEnv off K ρ' (Function.update E k v) := by
  intro k' hk'
  by_cases hkk : k' = k
  · subst hkk; simpa using hr
  · rw [Function.update_of_ne hkk]
    obtain ⟨h1, h2⟩ := h k' hk'
    refine ⟨?_, ?_⟩
    · rw [hf _ (by simp [zvar]; omega) (by simp [zvar]; omega) (by simp [zvar]; omega)]; exact h1
    · rw [hf _ (by simp [zvar]; omega) (by simp [zvar]; omega) (by simp [zvar]; omega)]; exact h2

theorem ReprEnv.frame {off K t : ℕ} {ρ ρ' : ℕ → ℕ} {E : ℕ → ℤ} (h : ReprEnv off K ρ E)
    (ht : off + 2 * K ≤ t) (hf : ∀ i < t, ρ' i = ρ i) : ReprEnv off K ρ' E := by
  intro k hk
  obtain ⟨h1, h2⟩ := h k hk
  exact ⟨by rw [hf _ (by simp [zvar]; omega)]; exact h1, by rw [hf _ (by simp [zvar]; omega)]; exact h2⟩

theorem ZOp.compile_spec {off K k t : ℕ} {o : ZOp} {ρ : ℕ → ℕ} {E : ℕ → ℤ} (hk : k < K)
    (ho : o.VarsBelow K) (ht : off + 2 * K ≤ t) (h : ReprEnv off K ρ E) :
    SContract (o.compile off k t) (zvar off k) t ρ (o.eval E) := by
  have hb := zvar_below hk ht
  have hne := zvar_ne off k
  cases o with
  | const c => exact sConst_spec c t hne ρ
  | copy a => exact sCopy_spec hb (zvar_below ho ht) hne (h a ho)
  | add a b => exact sAdd_spec hb (zvar_below ho.1 ht) (zvar_below ho.2 ht) hne (h a ho.1) (h b ho.2)
  | sub a b => exact sSub_spec hb (zvar_below ho.1 ht) (zvar_below ho.2 ht) hne (h a ho.1) (h b ho.2)
  | mul a b => exact sMul_spec hb (zvar_below ho.1 ht) (zvar_below ho.2 ht) hne (h a ho.1) (h b ho.2)
  | neg a => exact sNeg_spec hb (zvar_below ho ht) hne (h a ho)
  | abs a => exact sAbs_spec hb (zvar_below ho ht) hne (h a ho)
  | div a b => exact sDiv_spec hb hne (h a ho.1) (h b ho.2)
  | mod a b => exact sMod_spec hb hne (h a ho.1) (h b ho.2)
  | nadd a b =>
    have := nOp_spec (o' := .add (zvar off a).mag (zvar off b).mag) hb hne ρ
    simpa [Op.eval, (h a ho.1).2, (h b ho.2).2, ZOp.eval, ZOp.compile] using this
  | nsub a b =>
    have := nOp_spec (o' := .sub (zvar off a).mag (zvar off b).mag) hb hne ρ
    simpa [Op.eval, (h a ho.1).2, (h b ho.2).2, ZOp.eval, ZOp.compile] using this
  | nmul a b =>
    have := nOp_spec (o' := .mul (zvar off a).mag (zvar off b).mag) hb hne ρ
    simpa [Op.eval, (h a ho.1).2, (h b ho.2).2, ZOp.eval, ZOp.compile] using this

/-- The outcome of the compiled statement corresponding to an integer outcome. -/
def ZSimOK (off K : ℕ) (S : Stmt) (ρ : ℕ → ℕ) : ZOutcome → Prop
  | .normal E' => ∃ ρ', BigStep S ρ (.normal ρ') ∧ ReprEnv off K ρ' E'
  | .accept => BigStep S ρ .accept
  | .reject => BigStep S ρ .reject

theorem ZSimOK.pre {off K : ℕ} {S S' : Stmt} {ρ ρ₁ : ℕ → ℕ} {o : ZOutcome}
    (h : ZSimOK off K S ρ₁ o) (hpre : ∀ {o'}, BigStep S ρ₁ o' → BigStep S' ρ o') :
    ZSimOK off K S' ρ o := by
  cases o with
  | normal E' => obtain ⟨ρ', h1, h2⟩ := h; exact ⟨ρ', hpre h1, h2⟩
  | accept => exact hpre h
  | reject => exact hpre h

/-- A signed branch: flag, zero, branch on `0 < flag`. -/
theorem signedIte_bigStep {off K t a b : ℕ} {eq : Bool} {s u : Stmt} {ρ : ℕ → ℕ} {E : ℕ → ℤ}
    (ha : a < K) (hb : b < K) (ht : off + 2 * K ≤ t) (h : ReprEnv off K ρ E) :
    ∃ ρ₂, ReprEnv off K ρ₂ E ∧ (∀ i < t, ρ₂ i = ρ i) ∧
      ∀ {o}, BigStep (if (if eq then E a = E b else E a < E b) then s else u) ρ₂ o →
        BigStep (signedIte off eq a b t s u) ρ o := by
  have hf : t ≠ (zvar off a).sign ∧ t ≠ (zvar off a).mag ∧ t ≠ (zvar off b).sign ∧
      t ≠ (zvar off b).mag := by simp [zvar]; omega
  have key : ∀ (P : Prop) [Decidable P] (S : Stmt), FlagContract S t ρ P →
      ∃ ρ₂, ReprEnv off K ρ₂ E ∧ (∀ i < t, ρ₂ i = ρ i) ∧ ∀ {o}, BigStep (if P then s else u) ρ₂ o →
        BigStep (S ;; asg (t + 1) (.const 0) ;; .ifLt (t + 1) t s u) ρ o := by
    intro P _ S ⟨hp, hv, hfr⟩
    refine ⟨Function.update (S.execF ρ) (t + 1) 0, ?_, ?_, ?_⟩
    · exact h.frame ht (fun i hi => by
        rw [Function.update_of_ne (by omega), hfr i (by omega)])
    · intro i hi; rw [Function.update_of_ne (by omega), hfr i (by omega)]
    · intro o ho
      refine BigStep.seqNormal (bigStep_execF hp ρ) (BigStep.seqNormal (BigStep.assign _ _ _) ?_)
      by_cases hP : P
      · rw [ite_eq_left hP] at ho
        exact BigStep.ifLtTrue (by simp [Op.eval, Function.update_of_ne, hv, hP]) ho
      · rw [ite_eq_right hP] at ho
        exact BigStep.ifLtFalse (by simp [Op.eval, Function.update_of_ne, hv, hP]) ho
  cases eq with
  | false => exact key _ _ (sLtFlag_spec hf (h a ha) (h b hb))
  | true => exact key _ _ (sEqFlag_spec hf (h a ha) (h b hb))

/-- **Simulation of the integer layer.** -/
theorem ZStmt.compile_sim {off K : ℕ} {S : ZStmt} {E : ℕ → ℤ} {o : ZOutcome}
    (h : ZBigStep S E o) : S.VarsBelow K → ∀ t, off + 2 * K ≤ t → ∀ ρ, ReprEnv off K ρ E →
      ZSimOK off K (S.compile off t) ρ o := by
  induction h with
  | assign k o E =>
    intro hS t ht ρ hρ
    obtain ⟨ρ', h1, h2, h3⟩ := ZOp.compile_spec hS.1 hS.2 ht hρ
    exact ⟨ρ', h1, hρ.update ht h2 h3⟩
  | skip E =>
    intro hS t ht ρ hρ
    exact ⟨_, BigStep.assign _ _ _, hρ.frame ht (fun i hi => Function.update_of_ne (by omega) _ _)⟩
  | seqNormal h₁ h₂ ih₁ ih₂ =>
    intro hS t ht ρ hρ
    obtain ⟨ρ₁, b₁, r₁⟩ := ih₁ hS.1 t ht ρ hρ
    exact (ih₂ hS.2 t ht ρ₁ r₁).pre (fun h => BigStep.seqNormal b₁ h)
  | seqAccept h₁ ih₁ =>
    intro hS t ht ρ hρ; exact BigStep.seqAccept (ih₁ hS.1 t ht ρ hρ)
  | seqReject h₁ ih₁ =>
    intro hS t ht ρ hρ; exact BigStep.seqReject (ih₁ hS.1 t ht ρ hρ)
  | @iteTrue c s u E o hc h₁ ih =>
    intro hS t ht ρ hρ
    cases c with
    | nlt a b =>
      exact (ih hS.2.1 t ht ρ hρ).pre (fun h => BigStep.ifLtTrue (by
        rw [(hρ a hS.1.1).2, (hρ b hS.1.2).2]; exact hc) h)
    | neq a b =>
      exact (ih hS.2.1 t ht ρ hρ).pre (fun h => BigStep.ifEqTrue (by
        rw [(hρ a hS.1.1).2, (hρ b hS.1.2).2]; exact hc) h)
    | lt a b =>
      obtain ⟨ρ₂, r₂, f₂, hb⟩ := signedIte_bigStep (eq := false) (s := s.compile off (t + 2))
        (u := u.compile off (t + 2)) hS.1.1 hS.1.2 ht hρ
      exact (ih hS.2.1 (t + 2) (by omega) ρ₂ r₂).pre (fun h => hb (by
        simp only [Bool.false_eq_true, ite_false]; rw [ite_eq_left (show E a < E b from hc)]; exact h))
    | eq a b =>
      obtain ⟨ρ₂, r₂, f₂, hb⟩ := signedIte_bigStep (eq := true) (s := s.compile off (t + 2))
        (u := u.compile off (t + 2)) hS.1.1 hS.1.2 ht hρ
      exact (ih hS.2.1 (t + 2) (by omega) ρ₂ r₂).pre (fun h => hb (by
        simp only [ite_true]; rw [ite_eq_left (show E a = E b from hc)]; exact h))
  | @iteFalse c s u E o hc h₁ ih =>
    intro hS t ht ρ hρ
    cases c with
    | nlt a b =>
      exact (ih hS.2.2 t ht ρ hρ).pre (fun h => BigStep.ifLtFalse (by
        rw [(hρ a hS.1.1).2, (hρ b hS.1.2).2]; exact hc) h)
    | neq a b =>
      exact (ih hS.2.2 t ht ρ hρ).pre (fun h => BigStep.ifEqFalse (by
        rw [(hρ a hS.1.1).2, (hρ b hS.1.2).2]; exact hc) h)
    | lt a b =>
      obtain ⟨ρ₂, r₂, f₂, hb⟩ := signedIte_bigStep (eq := false) (s := s.compile off (t + 2))
        (u := u.compile off (t + 2)) hS.1.1 hS.1.2 ht hρ
      exact (ih hS.2.2 (t + 2) (by omega) ρ₂ r₂).pre (fun h => hb (by
        simp only [Bool.false_eq_true, ite_false]; rw [ite_eq_right (show ¬ E a < E b from hc)]; exact h))
    | eq a b =>
      obtain ⟨ρ₂, r₂, f₂, hb⟩ := signedIte_bigStep (eq := true) (s := s.compile off (t + 2))
        (u := u.compile off (t + 2)) hS.1.1 hS.1.2 ht hρ
      exact (ih hS.2.2 (t + 2) (by omega) ρ₂ r₂).pre (fun h => hb (by
        simp only [ite_true]; rw [ite_eq_right (show ¬ E a = E b from hc)]; exact h))
  | @loopFalse a b s E hc =>
    intro hS t ht ρ hρ
    exact ⟨ρ, BigStep.whileFalse (by rw [(hρ a hS.1).2, (hρ b hS.2.1).2]; exact hc), hρ⟩
  | @loopNormal a b s E E₁ o hc h₁ h₂ ih₁ ih₂ =>
    intro hS t ht ρ hρ
    obtain ⟨ρ₁, b₁, r₁⟩ := ih₁ hS.2.2 t ht ρ hρ
    exact (ih₂ hS t ht ρ₁ r₁).pre (fun h => BigStep.whileNormal
      (by rw [(hρ a hS.1).2, (hρ b hS.2.1).2]; exact hc) b₁ h)
  | @loopAccept a b s E hc h₁ ih =>
    intro hS t ht ρ hρ
    exact BigStep.whileAccept (by rw [(hρ a hS.1).2, (hρ b hS.2.1).2]; exact hc)
      (ih hS.2.2 t ht ρ hρ)
  | @loopReject a b s E hc h₁ ih =>
    intro hS t ht ρ hρ
    exact BigStep.whileReject (by rw [(hρ a hS.1).2, (hρ b hS.2.1).2]; exact hc)
      (ih hS.2.2 t ht ρ hρ)
  | accept E => intro hS t ht ρ hρ; exact BigStep.accept ρ
  | reject E => intro hS t ht ρ hρ; exact BigStep.reject ρ

end ZInQ.Compiler.IR
