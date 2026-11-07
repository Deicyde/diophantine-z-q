import ZInQKernel.Compiler.Programs.Blocks

/-!
# Correctness of the lowering

Blueprint: `compiler/natural/programs/lowering-correct.md`.

`Sim J ρ σ`: the machine file `σ` agrees with the ideal file `ρ` below the bound `J` and is
zero from `J` on (jump and auxiliary registers). Item 0 is `code_forward` (a derivation gives
a run of the open code to its normal exit, to the `accept` target or to the `reject` target)
and `code_backward` (a run from the entry that reaches a halting state yields a derivation,
by induction on the statement and, for loops, strong induction on the length of the run).
Items 1 and 2 are `lower_accepts_of_accepts` and `accepts_of_lower_halts`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace ZInQ.Compiler.IR

open RM

/-- The machine file `σ` simulates the ideal file `ρ` for the bound `J`. -/
def Sim (J : ℕ) (ρ σ : ℕ → ℕ) : Prop := (∀ i < J, σ i = ρ i) ∧ ∀ i, J ≤ i → σ i = 0

theorem Op.eval_congr {J : ℕ} {ρ σ : ℕ → ℕ} (h : ∀ i < J, σ i = ρ i) {o : Op}
    (ho : o.RegsBelow J) : o.eval σ = o.eval ρ := by
  cases o with
  | const k => rfl
  | copy y => simp [Op.eval, h y ho]
  | add y z | sub y z | mul y z | div y z | mod y z => simp [Op.eval, h y ho.1, h z ho.2]

theorem Sim.update {J x : ℕ} {ρ σ : ℕ → ℕ} (h : Sim J ρ σ) (hx : x < J) (v : ℕ) :
    Sim J (Function.update ρ x v) (fun i => if i = x then v else σ i) := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · by_cases hix : i = x
    · subst hix; simp
    · simp [hix, h.1 i hi]
  · have : i ≠ x := by omega
    simp [this, h.2 i hi]

/-- The outcome of a forward simulation of a statement at `s` with exits `acc`, `rej`. -/
def FwdOK (J : ℕ) (μ : Machine) (s len acc rej : ℕ) (σ : ℕ → ℕ) : Outcome → Prop
  | .normal ρ' => ∃ σ', Sim J ρ' σ' ∧ Reaches μ ⟨s, σ⟩ ⟨s + len, σ'⟩
  | .accept => ∃ σ', (∀ i, J ≤ i → σ' i = 0) ∧ Reaches μ ⟨s, σ⟩ ⟨acc, σ'⟩
  | .reject => ∃ σ', Reaches μ ⟨s, σ⟩ ⟨rej, σ'⟩

theorem FwdOK.pre {J : ℕ} {μ : Machine} {s s' len len' acc rej : ℕ} {σ σ₀ : ℕ → ℕ} {o : Outcome}
    (h : FwdOK J μ s' len' acc rej σ o) (hr : Reaches μ ⟨s, σ₀⟩ ⟨s', σ⟩)
    (hn : ∀ σ' : ℕ → ℕ, σ' J = 0 → Reaches μ ⟨s' + len', σ'⟩ ⟨s + len, σ'⟩) :
    FwdOK J μ s len acc rej σ₀ o := by
  cases o with
  | normal ρ' =>
    obtain ⟨σ', h1, h2⟩ := h; exact ⟨σ', h1, hr.trans (h2.trans (hn σ' (h1.2 J le_rfl)))⟩
  | accept => obtain ⟨σ', h1, h2⟩ := h; exact ⟨σ', h1, hr.trans h2⟩
  | reject => obtain ⟨σ', h2⟩ := h; exact ⟨σ', hr.trans h2⟩

theorem Embedded.jmp {μ : Machine} {s J x : ℕ} (he : Embedded μ s [jmp J x]) {σ : ℕ → ℕ}
    (hJ : σ J = 0) : Reaches μ ⟨s, σ⟩ ⟨x, σ⟩ :=
  (Reaches.refl _ _).of_step (step_jmp he.head hJ)

/-- **Item 0, forward**: a derivation `⟨S, ρ⟩ ⇓ o` gives a run of the open code. -/
theorem code_forward {J : ℕ} {S : Stmt} {ρ : ℕ → ℕ} {o : Outcome} (h : BigStep S ρ o) :
    S.RegsBelow J → ∀ {μ : Machine} {s acc rej : ℕ}, Embedded μ s (code J S s acc rej) →
      ∀ σ, Sim J ρ σ → FwdOK J μ s S.len acc rej σ o := by
  induction h with
  | assign x o ρ =>
    intro hS μ s acc rej he σ hσ
    refine ⟨_, hσ.update hS.1 (o.eval ρ), ?_⟩
    have := assignB_reaches hS.1 hS.2 he σ hσ.2
    rwa [Op.eval_congr hσ.1 hS.2] at this
  | @seqNormal S T ρ ρ₁ o h₁ h₂ ih₁ ih₂ =>
    intro hS μ s acc rej he σ hσ
    obtain ⟨he1, he2⟩ := he.split
    rw [code_length] at he2
    obtain ⟨σ₁, hσ₁, r₁⟩ := ih₁ hS.1 he1 σ hσ
    exact (ih₂ hS.2 he2 σ₁ hσ₁).pre r₁ (fun σ' _ => (Reaches.refl _ _).state_eq (by simp [Stmt.len]; omega))
  | seqAccept h₁ ih₁ =>
    intro hS μ s acc rej he σ hσ
    exact ih₁ hS.1 he.split.1 σ hσ
  | seqReject h₁ ih₁ =>
    intro hS μ s acc rej he σ hσ
    exact ih₁ hS.1 he.split.1 σ hσ
  | @ifLtTrue y z S T ρ o hc h₁ ih =>
    intro hS μ s acc rej he σ hσ
    obtain ⟨he, heT⟩ := he.split; obtain ⟨he, hej⟩ := he.split; obtain ⟨het, heS⟩ := he.split
    simp only [List.length_append, code_length, ltTest, snap2_length, List.length_cons,
      List.length_nil] at heS hej heT
    have rt := ltTest_reaches hS.1 hS.2.1 het σ hσ.2
    rw [hσ.1 y hS.1, hσ.1 z hS.2.1, ite_eq_left hc] at rt
    refine (ih hS.2.2.1 (heS.shift (by omega)) σ hσ).pre rt (fun σ' hJ => ?_)
    exact ((hej.shift (by omega)).jmp hJ).state_eq (by simp [Stmt.len]; omega)
  | @ifLtFalse y z S T ρ o hc h₁ ih =>
    intro hS μ s acc rej he σ hσ
    obtain ⟨he, heT⟩ := he.split; obtain ⟨he, hej⟩ := he.split; obtain ⟨het, heS⟩ := he.split
    simp only [List.length_append, code_length, ltTest, snap2_length, List.length_cons,
      List.length_nil] at heS hej heT
    have rt := ltTest_reaches hS.1 hS.2.1 het σ hσ.2
    rw [hσ.1 y hS.1, hσ.1 z hS.2.1, ite_eq_right hc] at rt
    refine (ih hS.2.2.2 (heT.shift (by omega)) σ hσ).pre rt (fun σ' _ => ?_)
    exact (Reaches.refl _ _).state_eq (by simp [Stmt.len]; omega)
  | @ifEqTrue y z S T ρ o hc h₁ ih =>
    intro hS μ s acc rej he σ hσ
    obtain ⟨he, heT⟩ := he.split; obtain ⟨he, hej⟩ := he.split; obtain ⟨het, heS⟩ := he.split
    simp only [List.length_append, code_length, eqTest, snap2_length, List.length_cons,
      List.length_nil] at heS hej heT
    have rt := eqTest_reaches hS.1 hS.2.1 het σ hσ.2
    rw [hσ.1 y hS.1, hσ.1 z hS.2.1, ite_eq_left hc] at rt
    refine (ih hS.2.2.1 (heS.shift (by omega)) σ hσ).pre rt (fun σ' hJ => ?_)
    exact ((hej.shift (by omega)).jmp hJ).state_eq (by simp [Stmt.len]; omega)
  | @ifEqFalse y z S T ρ o hc h₁ ih =>
    intro hS μ s acc rej he σ hσ
    obtain ⟨he, heT⟩ := he.split; obtain ⟨he, hej⟩ := he.split; obtain ⟨het, heS⟩ := he.split
    simp only [List.length_append, code_length, eqTest, snap2_length, List.length_cons,
      List.length_nil] at heS hej heT
    have rt := eqTest_reaches hS.1 hS.2.1 het σ hσ.2
    rw [hσ.1 y hS.1, hσ.1 z hS.2.1, ite_eq_right hc] at rt
    refine (ih hS.2.2.2 (heT.shift (by omega)) σ hσ).pre rt (fun σ' _ => ?_)
    exact (Reaches.refl _ _).state_eq (by simp [Stmt.len]; omega)
  | @whileFalse y z S ρ hc =>
    intro hS μ s acc rej he σ hσ
    obtain ⟨he, hej⟩ := he.split; obtain ⟨het, heS⟩ := he.split
    have rt := ltTest_reaches hS.1 hS.2.1 het σ hσ.2
    rw [hσ.1 y hS.1, hσ.1 z hS.2.1, ite_eq_right hc] at rt
    exact ⟨σ, hσ, rt.state_eq (by simp [Stmt.len]; omega)⟩
  | @whileNormal y z S ρ ρ₁ o hc h₁ h₂ ih₁ ih₂ =>
    intro hS μ s acc rej he σ hσ
    have he0 := he
    obtain ⟨he, hej⟩ := he.split; obtain ⟨het, heS⟩ := he.split
    simp only [List.length_append, code_length, ltTest, snap2_length, List.length_cons,
      List.length_nil] at heS hej
    have rt := ltTest_reaches hS.1 hS.2.1 het σ hσ.2
    rw [hσ.1 y hS.1, hσ.1 z hS.2.1, ite_eq_left hc] at rt
    obtain ⟨σ₁, hσ₁, r₁⟩ := ih₁ hS.2.2 (heS.shift (by omega)) σ hσ
    have rj := (hej.shift (show _ = s + 20 + S.len by omega)).jmp (hσ₁.2 J le_rfl)
    exact (ih₂ hS he0 σ₁ hσ₁).pre (rt.trans (r₁.trans rj)) (fun σ' _ => Reaches.refl _ _)
  | @whileAccept y z S ρ hc h₁ ih =>
    intro hS μ s acc rej he σ hσ
    obtain ⟨he, hej⟩ := he.split; obtain ⟨het, heS⟩ := he.split
    simp only [List.length_append, code_length, ltTest, snap2_length, List.length_cons,
      List.length_nil] at heS hej
    have rt := ltTest_reaches hS.1 hS.2.1 het σ hσ.2
    rw [hσ.1 y hS.1, hσ.1 z hS.2.1, ite_eq_left hc] at rt
    obtain ⟨σ', h1, h2⟩ := (ih hS.2.2 (heS.shift (by omega)) σ hσ); exact ⟨σ', h1, rt.trans h2⟩
  | @whileReject y z S ρ hc h₁ ih =>
    intro hS μ s acc rej he σ hσ
    obtain ⟨he, hej⟩ := he.split; obtain ⟨het, heS⟩ := he.split
    simp only [List.length_append, code_length, ltTest, snap2_length, List.length_cons,
      List.length_nil] at heS hej
    have rt := ltTest_reaches hS.1 hS.2.1 het σ hσ.2
    rw [hσ.1 y hS.1, hσ.1 z hS.2.1, ite_eq_left hc] at rt
    obtain ⟨σ', h2⟩ := (ih hS.2.2 (heS.shift (by omega)) σ hσ); exact ⟨σ', rt.trans h2⟩
  | accept ρ =>
    intro hS μ s acc rej he σ hσ
    exact ⟨σ, hσ.2, he.jmp (hσ.2 J le_rfl)⟩
  | reject ρ =>
    intro hS μ s acc rej he σ hσ
    exact ⟨σ, he.jmp (hσ.2 J le_rfl)⟩


/-! ### Backward direction -/

/-- The run from `c` reaches a configuration at the halting state `F` after `t` steps. -/
def HaltsIn (μ : Machine) (F t : ℕ) (c : Config) : Prop :=
  ∃ h, ReachesIn μ t c h ∧ h.state = F

theorem HaltsIn.state_eq {μ : Machine} {F t a b : ℕ} {σ : ℕ → ℕ} (h : HaltsIn μ F t ⟨a, σ⟩)
    (e : a = b) : HaltsIn μ F t ⟨b, σ⟩ := e ▸ h

theorem HaltsIn.of_reaches {μ : Machine} {F t : ℕ} (hF : μ F = .halt) {c d : Config}
    (hr : Reaches μ c d) (hh : HaltsIn μ F t c) : ∃ t' ≤ t, HaltsIn μ F t' d := by
  obtain ⟨k, hk⟩ := hr
  obtain ⟨h, ht, hs⟩ := hh
  obtain ⟨hle, h'⟩ := halts_after hk ht (by rw [hs]; exact hF)
  exact ⟨t - k, by omega, h, h', hs⟩

theorem HaltsIn.of_step {μ : Machine} {F t : ℕ} (hF : μ F = .halt) {c d : Config}
    (hs : step μ c = some d) (hh : HaltsIn μ F t c) : ∃ t' < t, HaltsIn μ F t' d := by
  obtain ⟨h, ht, hst⟩ := hh
  obtain ⟨hle, h'⟩ := halts_after (k := 1) (d := d) (by simp [ReachesIn, stepN_succ, hs]) ht
    (by rw [hst]; exact hF)
  exact ⟨t - 1, by omega, h, h', hst⟩

/-- The disjunction of the backward simulation. -/
def BwdOK (J : ℕ) (μ : Machine) (F : ℕ) (S : Stmt) (s rej t : ℕ) (ρ : ℕ → ℕ) : Prop :=
  BigStep S ρ .accept ∨
    (∃ ρ' σ' t', t' ≤ t ∧ BigStep S ρ (.normal ρ') ∧ Sim J ρ' σ' ∧
      HaltsIn μ F t' ⟨s + S.len, σ'⟩) ∨
    (∃ σ' t', t' ≤ t ∧ BigStep S ρ .reject ∧ HaltsIn μ F t' ⟨rej, σ'⟩)

/-- **Item 0, backward**: a run from the entry of the open code that reaches the halting state
yields a derivation of `accept`, or of a normal outcome followed by a halting run from the
normal exit, or of `reject` followed by a halting run from the reject target. -/
theorem code_backward {J : ℕ} {μ : Machine} {F : ℕ} (hF : μ F = .halt) :
    ∀ (S : Stmt), S.RegsBelow J → ∀ {s acc rej : ℕ}, Embedded μ s (code J S s acc rej) →
      ∀ t ρ σ, Sim J ρ σ → HaltsIn μ F t ⟨s, σ⟩ → BwdOK J μ F S s rej t ρ
  | .assign x o, hS, s, acc, rej, he, t, ρ, σ, hσ, hh => by
    obtain ⟨σ', hσ', r⟩ := code_forward (BigStep.assign x o ρ) hS he σ hσ
    obtain ⟨t', ht', hh'⟩ := hh.of_reaches hF r
    exact Or.inr (Or.inl ⟨_, σ', t', ht', BigStep.assign x o ρ, hσ', hh'⟩)
  | .seq S T, hS, s, acc, rej, he, t, ρ, σ, hσ, hh => by
    obtain ⟨he1, he2⟩ := he.split
    rw [code_length] at he2
    rcases code_backward hF S hS.1 he1 t ρ σ hσ hh with h | ⟨ρ₁, σ₁, t₁, ht₁, h₁, hσ₁, hh₁⟩ |
        ⟨σ₁, t₁, ht₁, h₁, hh₁⟩
    · exact Or.inl (BigStep.seqAccept h)
    · rcases code_backward hF T hS.2 he2 t₁ ρ₁ σ₁ hσ₁ hh₁ with h | ⟨ρ₂, σ₂, t₂, ht₂, h₂, hσ₂, hh₂⟩ |
          ⟨σ₂, t₂, ht₂, h₂, hh₂⟩
      · exact Or.inl (BigStep.seqNormal h₁ h)
      · exact Or.inr (Or.inl ⟨ρ₂, σ₂, t₂, by omega, BigStep.seqNormal h₁ h₂, hσ₂,
          hh₂.state_eq (by simp [Stmt.len]; omega)⟩)
      · exact Or.inr (Or.inr ⟨σ₂, t₂, by omega, BigStep.seqNormal h₁ h₂, hh₂⟩)
    · exact Or.inr (Or.inr ⟨σ₁, t₁, ht₁, BigStep.seqReject h₁, hh₁⟩)
  | .ifLt y z S T, hS, s, acc, rej, he, t, ρ, σ, hσ, hh => by
    obtain ⟨he, heT⟩ := he.split; obtain ⟨he, hej⟩ := he.split; obtain ⟨het, heS⟩ := he.split
    simp only [List.length_append, code_length, ltTest, snap2_length, List.length_cons,
      List.length_nil] at heS hej heT
    have rt := ltTest_reaches hS.1 hS.2.1 het σ hσ.2
    rw [hσ.1 y hS.1, hσ.1 z hS.2.1] at rt
    obtain ⟨t₀, ht₀, hh₀⟩ := hh.of_reaches hF rt
    by_cases hc : ρ y < ρ z
    · rw [ite_eq_left hc] at hh₀
      rcases code_backward hF S hS.2.2.1 (heS.shift (by omega)) t₀ ρ σ hσ hh₀ with h |
          ⟨ρ₁, σ₁, t₁, ht₁, h₁, hσ₁, hh₁⟩ | ⟨σ₁, t₁, ht₁, h₁, hh₁⟩
      · exact Or.inl (BigStep.ifLtTrue hc h)
      · obtain ⟨t₂, ht₂, hh₂⟩ := hh₁.of_reaches hF
          ((hej.shift (show _ = s + 20 + S.len by omega)).jmp (hσ₁.2 J le_rfl))
        exact Or.inr (Or.inl ⟨ρ₁, σ₁, t₂, by omega, BigStep.ifLtTrue hc h₁, hσ₁,
          hh₂.state_eq (by simp [Stmt.len]; omega)⟩)
      · exact Or.inr (Or.inr ⟨σ₁, t₁, by omega, BigStep.ifLtTrue hc h₁, hh₁⟩)
    · rw [ite_eq_right hc] at hh₀
      rcases code_backward hF T hS.2.2.2 (heT.shift (by omega)) t₀ ρ σ hσ hh₀ with h |
          ⟨ρ₁, σ₁, t₁, ht₁, h₁, hσ₁, hh₁⟩ | ⟨σ₁, t₁, ht₁, h₁, hh₁⟩
      · exact Or.inl (BigStep.ifLtFalse hc h)
      · exact Or.inr (Or.inl ⟨ρ₁, σ₁, t₁, by omega, BigStep.ifLtFalse hc h₁, hσ₁,
          hh₁.state_eq (by simp [Stmt.len]; omega)⟩)
      · exact Or.inr (Or.inr ⟨σ₁, t₁, by omega, BigStep.ifLtFalse hc h₁, hh₁⟩)
  | .ifEq y z S T, hS, s, acc, rej, he, t, ρ, σ, hσ, hh => by
    obtain ⟨he, heT⟩ := he.split; obtain ⟨he, hej⟩ := he.split; obtain ⟨het, heS⟩ := he.split
    simp only [List.length_append, code_length, eqTest, snap2_length, List.length_cons,
      List.length_nil] at heS hej heT
    have rt := eqTest_reaches hS.1 hS.2.1 het σ hσ.2
    rw [hσ.1 y hS.1, hσ.1 z hS.2.1] at rt
    obtain ⟨t₀, ht₀, hh₀⟩ := hh.of_reaches hF rt
    by_cases hc : ρ y = ρ z
    · rw [ite_eq_left hc] at hh₀
      rcases code_backward hF S hS.2.2.1 (heS.shift (by omega)) t₀ ρ σ hσ hh₀ with h |
          ⟨ρ₁, σ₁, t₁, ht₁, h₁, hσ₁, hh₁⟩ | ⟨σ₁, t₁, ht₁, h₁, hh₁⟩
      · exact Or.inl (BigStep.ifEqTrue hc h)
      · obtain ⟨t₂, ht₂, hh₂⟩ := hh₁.of_reaches hF
          ((hej.shift (show _ = s + 22 + S.len by omega)).jmp (hσ₁.2 J le_rfl))
        exact Or.inr (Or.inl ⟨ρ₁, σ₁, t₂, by omega, BigStep.ifEqTrue hc h₁, hσ₁,
          hh₂.state_eq (by simp [Stmt.len]; omega)⟩)
      · exact Or.inr (Or.inr ⟨σ₁, t₁, by omega, BigStep.ifEqTrue hc h₁, hh₁⟩)
    · rw [ite_eq_right hc] at hh₀
      rcases code_backward hF T hS.2.2.2 (heT.shift (by omega)) t₀ ρ σ hσ hh₀ with h |
          ⟨ρ₁, σ₁, t₁, ht₁, h₁, hσ₁, hh₁⟩ | ⟨σ₁, t₁, ht₁, h₁, hh₁⟩
      · exact Or.inl (BigStep.ifEqFalse hc h)
      · exact Or.inr (Or.inl ⟨ρ₁, σ₁, t₁, by omega, BigStep.ifEqFalse hc h₁, hσ₁,
          hh₁.state_eq (by simp [Stmt.len]; omega)⟩)
      · exact Or.inr (Or.inr ⟨σ₁, t₁, by omega, BigStep.ifEqFalse hc h₁, hh₁⟩)
  | .whileLt y z S, hS, s, acc, rej, he, t, ρ, σ, hσ, hh => by
    have he0 := he
    obtain ⟨he, hej⟩ := he.split; obtain ⟨het, heS⟩ := he.split
    simp only [List.length_append, code_length, ltTest, snap2_length, List.length_cons,
      List.length_nil] at heS hej
    induction t using Nat.strong_induction_on generalizing ρ σ with
    | _ t ihT =>
      have rt := ltTest_reaches hS.1 hS.2.1 het σ hσ.2
      rw [hσ.1 y hS.1, hσ.1 z hS.2.1] at rt
      obtain ⟨t₀, ht₀, hh₀⟩ := hh.of_reaches hF rt
      by_cases hc : ρ y < ρ z
      · rw [ite_eq_left hc] at hh₀
        rcases code_backward hF S hS.2.2 (heS.shift (by omega)) t₀ ρ σ hσ hh₀ with h |
            ⟨ρ₁, σ₁, t₁, ht₁, h₁, hσ₁, hh₁⟩ | ⟨σ₁, t₁, ht₁, h₁, hh₁⟩
        · exact Or.inl (BigStep.whileAccept hc h)
        · obtain ⟨t₂, ht₂, hh₂⟩ := hh₁.of_step hF (step_jmp
            ((hej.shift (show _ = s + 20 + S.len by omega)).head) (hσ₁.2 J le_rfl))
          rcases ihT t₂ (by omega) ρ₁ σ₁ hσ₁ hh₂ with h | ⟨ρ₂, σ₂, t₃, ht₃, h₂, hσ₂, hh₃⟩ |
              ⟨σ₂, t₃, ht₃, h₂, hh₃⟩
          · exact Or.inl (BigStep.whileNormal hc h₁ h)
          · exact Or.inr (Or.inl ⟨ρ₂, σ₂, t₃, by omega, BigStep.whileNormal hc h₁ h₂, hσ₂, hh₃⟩)
          · exact Or.inr (Or.inr ⟨σ₂, t₃, by omega, BigStep.whileNormal hc h₁ h₂, hh₃⟩)
        · exact Or.inr (Or.inr ⟨σ₁, t₁, by omega, BigStep.whileReject hc h₁, hh₁⟩)
      · rw [ite_eq_right hc] at hh₀
        exact Or.inr (Or.inl ⟨ρ, σ, t₀, ht₀, BigStep.whileFalse hc, hσ,
          hh₀.state_eq (by simp [Stmt.len]; omega)⟩)
  | .accept, hS, s, acc, rej, he, t, ρ, σ, hσ, hh => Or.inl (BigStep.accept ρ)
  | .reject, hS, s, acc, rej, he, t, ρ, σ, hσ, hh => by
    obtain ⟨t', ht', hh'⟩ := hh.of_reaches hF (he.jmp (hσ.2 J le_rfl))
    exact Or.inr (Or.inr ⟨σ, t', ht', BigStep.reject ρ, hh'⟩)


/-! ### The closed program -/

theorem embedded_self (L : List Instr) : Embedded (RM.Program.toMachine L) 0 L := by
  intro i hi; rw [toMachine_of_lt _ (by omega)]; simp

/-- The permanent self-loop never reaches another state. -/
theorem selfLoop_stays {μ : Machine} {n J : ℕ} (h : μ n = jmp J n) :
    ∀ t (σ : ℕ → ℕ) c, ReachesIn μ t ⟨n, σ⟩ c → c.state = n := by
  intro t
  induction t with
  | zero => intro σ c hc; simp [ReachesIn] at hc; rw [← hc]
  | succ t ih =>
    intro σ c hc
    unfold ReachesIn at hc
    rw [stepN_succ] at hc
    by_cases hJ : σ J = 0
    · rw [step_dec_zero (by rw [h]; rfl) hJ] at hc; exact ih _ _ hc
    · rw [step_dec_pos (by rw [h]; rfl) hJ] at hc; exact ih _ _ hc

theorem cleanup_getElem (r b i : ℕ) (hi : i < (cleanup r b).length) :
    (cleanup r b)[i] = .dec i (b + i) (b + i + 1) := by
  simp [cleanup]

/-- The cleanup clears the registers below `r`. -/
theorem cleanup_reaches {μ : Machine} {r b : ℕ} (he : Embedded μ b (cleanup r b)) (σ : ℕ → ℕ) :
    ∀ k ≤ r, Reaches μ ⟨b, σ⟩ ⟨b + k, fun i => if i < k then 0 else σ i⟩
  | 0, _ => (Reaches.refl _ _).regs_eq (by funext i; simp)
  | k + 1, hk => by
    have h := he k (by simp [cleanup]; omega)
    rw [cleanup_getElem] at h
    refine ((cleanup_reaches he σ k (by omega)).trans (reaches_clear h _)).state_eq (by omega)
      |>.regs_eq ?_
    funext i; simp [Function.update_apply]; split_ifs <;> omega

section Lower

variable (P : Program)

theorem lower_eq : lower P = code P.bound P.body 0 (P.body.len + 1) P.body.len ++
    ([jmp P.bound P.body.len] ++ (cleanup P.regCount (P.body.len + 1) ++ [.halt])) := by
  simp [lower]

theorem lower_embedded :
    Embedded (lower P).toMachine 0 (code P.bound P.body 0 (P.body.len + 1) P.body.len) ∧
    (lower P).toMachine P.body.len = jmp P.bound P.body.len ∧
    Embedded (lower P).toMachine (P.body.len + 1) (cleanup P.regCount (P.body.len + 1)) ∧
    (lower P).toMachine (P.body.len + P.regCount + 1) = .halt := by
  have he := embedded_self (lower P)
  conv at he => arg 3; rw [lower_eq]
  obtain ⟨he1, he⟩ := he.split; obtain ⟨he2, he⟩ := he.split; obtain ⟨he3, he4⟩ := he.split
  simp only [code_length, List.length_cons, List.length_nil, Nat.zero_add] at he2 he3 he4
  refine ⟨he1, he2.head, he3.shift (show _ = P.body.len + 1 by omega), ?_⟩
  have := he4.head
  simp only [cleanup, List.length_map, List.length_range] at this
  rw [← this]; congr 1; omega

theorem lower_final : (lower P).length - 1 = P.body.len + P.regCount + 1 := by
  rw [lower_length]; omega

theorem sim_initFile (hP : P.WF) (a : Fin P.inputs → ℕ) :
    Sim P.bound (initFile a) (initFile a) :=
  ⟨fun _ _ => rfl, fun i hi => initFile_of_le a (le_trans hP.inputs_le hi)⟩

/-- **Item 1**: if `⟨S, ρ₀(a)⟩ ⇓ accept`, the lowering accepts `a`. -/
theorem lower_accepts_of_accepts (hP : P.WF) (a : Fin P.inputs → ℕ) (h : P.Accepts a) :
    (lower P).Accepts a := by
  obtain ⟨he, -, hc, -⟩ := lower_embedded P
  obtain ⟨σ', hz, r⟩ := code_forward h hP.regs he _ (sim_initFile P hP a)
  obtain ⟨t, ht⟩ := r.trans (cleanup_reaches hc σ' P.regCount le_rfl)
  refine ⟨t, _, ht, ?_, fun j => ?_⟩
  · rw [lower_final]; simp only; omega
  · simp only
    split_ifs with hj
    · rfl
    · exact hz j (by unfold Program.regCount at hj; omega)

/-- **Item 2**: if the lowering halts on `a`, then `⟨S, ρ₀(a)⟩ ⇓ accept`. -/
theorem accepts_of_lower_halts (hP : P.WF) (a : Fin P.inputs → ℕ) (h : (lower P).HaltsOn a) :
    P.Accepts a := by
  obtain ⟨he, hloop, -, hF⟩ := lower_embedded P
  obtain ⟨t, c, ht, hs⟩ := h
  rw [lower_final] at hs
  have hh : HaltsIn (lower P).toMachine (P.body.len + P.regCount + 1) t ⟨0, initFile a⟩ :=
    ⟨c, ht, hs⟩
  rcases code_backward hF P.body hP.regs he t _ _ (sim_initFile P hP a) hh with h |
      ⟨ρ', σ', t', -, -, -, ⟨c', hc', hs'⟩⟩ | ⟨σ', t', -, -, ⟨c', hc', hs'⟩⟩
  · exact h
  · rw [Nat.zero_add] at hc'
    have := selfLoop_stays hloop t' σ' c' hc'
    unfold Program.regCount at hs'; omega
  · have := selfLoop_stays hloop t' σ' c' hc'
    unfold Program.regCount at hs'; omega

/-- `low(S)` halts on `a` iff `S` accepts `a`. -/
theorem lower_halts_iff (hP : P.WF) (a : Fin P.inputs → ℕ) :
    (lower P).HaltsOn a ↔ P.Accepts a := by
  refine ⟨accepts_of_lower_halts P hP a, fun h => ?_⟩
  obtain ⟨t, c, ht, hs, -⟩ := lower_accepts_of_accepts P hP a h
  exact ⟨t, c, ht, hs⟩

/-- `low(S)` accepts `a` iff `S` accepts `a`. -/
theorem lower_accepts_iff (hP : P.WF) (a : Fin P.inputs → ℕ) :
    (lower P).Accepts a ↔ P.Accepts a := by
  refine ⟨fun h => accepts_of_lower_halts P hP a ?_, lower_accepts_of_accepts P hP a⟩
  obtain ⟨t, c, ht, hs, -⟩ := h
  exact ⟨t, c, ht, hs⟩

/-- **Correctness of the lowering**: `low(S)` halts on `a` iff it accepts `a` iff `S`
accepts `a`. -/
theorem lowering_correct (hP : P.WF) (a : Fin P.inputs → ℕ) :
    ((lower P).HaltsOn a ↔ (lower P).Accepts a) ∧ ((lower P).Accepts a ↔ P.Accepts a) :=
  ⟨(lower_halts_iff P hP a).trans (lower_accepts_iff P hP a).symm, lower_accepts_iff P hP a⟩

/-- For a program that rejects `a`, the run of `low(S)` never halts. -/
theorem lower_not_halts_of_reject (hP : P.WF) (a : Fin P.inputs → ℕ)
    (h : BigStep P.body (initFile a) .reject) : ¬ (lower P).HaltsOn a := fun hh =>
  Outcome.noConfusion ((accepts_of_lower_halts P hP a hh).deterministic h)

end Lower

end ZInQ.Compiler.IR
