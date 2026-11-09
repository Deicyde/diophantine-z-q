import ZInQKernel.Compiler.Circuits.MacroSemantics

/-!
# Private witnesses with exposed variables

A list of formulas produced on `[c₀, c₁)` may use some of its own fresh variables (the set `E`,
*exposed*) in later formulas, as the history variables of the packed construction are used by
all of its conjuncts. `SpecE φs U c₀ c₁ E R` says: the formulas use only variables of
`U ∪ [c₀, c₁)`, and for every `x` the private-witness statement over `[c₀, c₁) \ E` is
equivalent to `R x` (so `R` reads the exposed variables at `x`). Exposed variables are
quantified at the end (`SpecE.close`). This is item 2 of the compilation statement for
constructions whose fresh variables are shared among conjuncts.
-/

noncomputable section

namespace ZInQ.Compiler.Natural

open Syntax MvPolynomial

/-- `y` agrees with `x` outside the set `I`. -/
def AgreeOut (x y : ℕ → ℕ) (I : ℕ → Prop) : Prop := ∀ i, ¬ I i → y i = x i

/-- The specification of a list of formulas with exposed variables `E`. -/
structure SpecE (φs : List Formula) (U : Set ℕ) (c₀ c₁ : ℕ) (E : Set ℕ)
    (R : (ℕ → ℕ) → Prop) : Prop where
  le : c₀ ≤ c₁
  exp : ∀ i ∈ E, c₀ ≤ i ∧ i < c₁
  loc : ∀ φ ∈ φs, Local φ U c₀ c₁
  sem : ∀ x, (∃ y, AgreeOut x y (fun i => c₀ ≤ i ∧ i < c₁ ∧ i ∉ E) ∧ ∀ φ ∈ φs, NHolds y φ) ↔ R x

namespace SpecE

variable {φs φs₁ φs₂ : List Formula} {U : Set ℕ} {c₀ c₁ c₂ : ℕ} {E E₁ E₂ : Set ℕ}
  {R R₁ R₂ : (ℕ → ℕ) → Prop}

theorem congr (h : SpecE φs U c₀ c₁ E R) {R' : (ℕ → ℕ) → Prop} (hR : ∀ x, R x ↔ R' x) :
    SpecE φs U c₀ c₁ E R' := ⟨h.le, h.exp, h.loc, fun x => (h.sem x).trans (hR x)⟩

theorem of_eq (h : SpecE φs U c₀ c₁ E R) {φs' : List Formula} {E' : Set ℕ} (hφ : φs = φs')
    (hE : E = E') : SpecE φs' U c₀ c₁ E' R := by
  subst hφ hE; exact h

theorem mono (h : SpecE φs U c₀ c₁ E R) {U' : Set ℕ} (hU : U ⊆ U') : SpecE φs U' c₀ c₁ E R :=
  ⟨h.le, h.exp, fun φ hφ => (h.loc φ hφ).mono fun i hi => hi.imp_left fun h => hU h, h.sem⟩

theorem ofSpecL (h : SpecL φs U c₀ c₁ R) : SpecE φs U c₀ c₁ ∅ R :=
  ⟨h.le, by simp, h.loc, fun x => by
    rw [← h.sem x]
    refine exists_congr fun y => and_congr_left fun _ => forall_congr' fun i => ?_
    simp [Set.mem_empty_iff_false]⟩

theorem ofSpec {φ : Formula} (h : Spec φ U c₀ c₁ R) : SpecE [φ] U c₀ c₁ ∅ R :=
  ofSpecL ⟨h.le, by simpa using h.loc, fun x => by simpa using h.sem x⟩

/-- Fresh variables with no formula: all exposed. -/
theorem expose (U : Set ℕ) (c n : ℕ) :
    SpecE [] U c (c + n) {i | c ≤ i ∧ i < c + n} fun _ => True :=
  ⟨by omega, fun _ hi => hi, by simp, fun x => by
    simp only [List.not_mem_nil, false_imp_iff, implies_true, and_true, iff_true]
    exact ⟨x, fun _ _ => rfl⟩⟩

theorem nil (U : Set ℕ) (c : ℕ) : SpecE [] U c c ∅ fun _ => True := by
  have h := expose U c 0
  have he : {i | c ≤ i ∧ i < c + 0} = ∅ := by ext i; simp
  rw [he] at h
  exact h

/-- **Composition.** -/
theorem append (h₁ : SpecE φs₁ U c₀ c₁ E₁ R₁) (h₂ : SpecE φs₂ (U ∪ E₁) c₁ c₂ E₂ R₂)
    (hU : ∀ i ∈ U, i < c₀) :
    SpecE (φs₁ ++ φs₂) U c₀ c₂ (E₁ ∪ E₂) fun x => R₁ x ∧ R₂ x := by
  classical
  have h01 := h₁.le
  have h12 := h₂.le
  refine ⟨h01.trans h12, fun i hi => ?_, fun φ hφ => ?_, fun x => ?_⟩
  · rcases hi with hi | hi
    · have := h₁.exp i hi; omega
    · have := h₂.exp i hi; omega
  · rcases List.mem_append.1 hφ with hφ | hφ
    · exact (h₁.loc φ hφ).mono fun i hi => hi.imp_right fun hi => ⟨hi.1, by omega⟩
    · refine (h₂.loc φ hφ).mono fun i hi => ?_
      rcases hi with (hi | hi) | hi
      · exact Or.inl hi
      · have := h₁.exp i hi; exact Or.inr ⟨this.1, by omega⟩
      · exact Or.inr ⟨by omega, hi.2⟩
  constructor
  · rintro ⟨y, hy, hall⟩
    have hyx : ∀ i, (i < c₀ ∨ c₂ ≤ i ∨ i ∈ E₁ ∨ i ∈ E₂) → y i = x i := fun i hi =>
      hy i fun ⟨a, b, c⟩ => by
        rcases hi with hi | hi | hi | hi
        · omega
        · omega
        · exact c (Or.inl hi)
        · exact c (Or.inr hi)
    refine ⟨(h₁.sem x).1 ⟨fun i => if c₀ ≤ i ∧ i < c₁ ∧ i ∉ E₁ then y i else x i,
      fun i hi => by simp [hi], fun φ hφ => (nholds_congr fun i hi => ?_).1
        (hall φ (List.mem_append_left _ hφ))⟩,
      (h₂.sem x).1 ⟨fun i => if c₁ ≤ i ∧ i < c₂ ∧ i ∉ E₂ then y i else x i,
      fun i hi => by simp [hi], fun φ hφ => (nholds_congr fun i hi => ?_).1
        (hall φ (List.mem_append_right _ hφ))⟩⟩
    · split_ifs with hc
      · rfl
      · rcases h₁.loc φ hφ i hi with hU' | hI
        · exact hyx i (Or.inl (hU i hU'))
        · exact hyx i (Or.inr (Or.inr (Or.inl (by by_contra hn; exact hc ⟨hI.1, hI.2, hn⟩))))
    · split_ifs with hc
      · rfl
      · rcases h₂.loc φ hφ i hi with (hU' | hE) | hI
        · exact hyx i (Or.inl (hU i hU'))
        · exact hyx i (Or.inr (Or.inr (Or.inl hE)))
        · exact hyx i (Or.inr (Or.inr (Or.inr (by by_contra hn; exact hc ⟨hI.1, hI.2, hn⟩))))
  · rintro ⟨hR₁, hR₂⟩
    obtain ⟨y₁, hy₁, hφ₁⟩ := (h₁.sem x).2 hR₁
    obtain ⟨y₂, hy₂, hφ₂⟩ := (h₂.sem x).2 hR₂
    refine ⟨fun i => if i < c₁ then y₁ i else y₂ i, fun i hi => ?_, fun φ hφ => ?_⟩
    · simp only
      split_ifs with hc
      · refine hy₁ i fun ⟨a, b, c⟩ => hi ⟨a, by omega, fun hE => ?_⟩
        rcases hE with hE | hE
        · exact c hE
        · have := h₂.exp i hE; omega
      · refine hy₂ i fun ⟨a, b, c⟩ => hi ⟨by omega, b, fun hE => ?_⟩
        rcases hE with hE | hE
        · have := h₁.exp i hE; omega
        · exact c hE
    · rcases List.mem_append.1 hφ with hφ | hφ
      · refine (nholds_congr fun i hi => ?_).2 (hφ₁ φ hφ)
        rcases h₁.loc φ hφ i hi with hU' | hI
        · rw [ite_eq_left (by have := hU i hU'; omega)]
        · rw [ite_eq_left hI.2]
      · refine (nholds_congr fun i hi => ?_).2 (hφ₂ φ hφ)
        split_ifs with hc
        · rcases h₂.loc φ hφ i hi with (hU' | hE) | hI
          · rw [hy₁ i (by have := hU i hU'; omega), hy₂ i (by have := hU i hU'; omega)]
          · rw [hy₁ i (fun h => h.2.2 hE), hy₂ i (by intro h; have := h₁.exp i hE; omega)]
          · omega
        · rfl

/-- **Exposed variables are quantified at the end.** -/
theorem close (h : SpecE φs U c₀ c₁ E R) :
    Spec (.and φs) U c₀ c₁ fun x => ∃ z, AgreeOut x z (· ∈ E) ∧ R z := by
  classical
  refine ⟨h.le, local_and h.loc, fun x => ?_⟩
  simp only [nholds_and]
  constructor
  · rintro ⟨y, hy, hφ⟩
    refine ⟨fun i => if i ∈ E then y i else x i, fun i hi => by simp [hi], (h.sem _).1 ⟨y,
      fun i hi => ?_, hφ⟩⟩
    by_cases hE : i ∈ E
    · simp [hE]
    · simp only [hE, ite_false]
      exact hy i fun hc => hi ⟨hc.1, hc.2, hE⟩
  · rintro ⟨z, hz, hR⟩
    obtain ⟨y, hy, hφ⟩ := (h.sem z).2 hR
    refine ⟨y, fun i hi => ?_, hφ⟩
    have hE : i ∉ E := fun hE => hi (h.exp i hE)
    rw [hy i fun hc => hi ⟨hc.1, hc.2.1⟩, hz i hE]

end SpecE

/-! ### Formula lists of constructions -/

theorem SpecL.append' {φs₁ φs₂ : List Formula} {U : Set ℕ} {c₀ c₁ c₂ : ℕ}
    {R₁ R₂ : (ℕ → ℕ) → Prop} (h₁ : SpecL φs₁ U c₀ c₁ R₁) (h₂ : SpecL φs₂ U c₁ c₂ R₂)
    (hU : ∀ i ∈ U, i < c₀) : SpecL (φs₁ ++ φs₂) U c₀ c₂ fun x => R₁ x ∧ R₂ x := by
  have := (SpecE.ofSpecL h₁).append (by simpa using SpecE.ofSpecL h₂) hU
  exact ⟨this.le, this.loc, fun x => by rw [← this.sem x]; simp [Agree, AgreeOut]⟩

/-- A list of constructions, each satisfying `MSpec`, run in order. -/
theorem seqM_map_specL {τ : ExPoly} {γ : Type} {U : Set ℕ} (l : List γ) (g : γ → NM NForm)
    (Rg : γ → (ℕ → ℕ) → Prop) (h : ∀ x ∈ l, MSpec τ (g x) U (Rg x)) (s : State)
    (hs : ∀ i ∈ U, i < s.next) :
    SpecL ((seqM (l.map g) s).1.map (NForm.toFormula τ)) U s.next (seqM (l.map g) s).2.next
      fun x => ∀ y ∈ l, Rg y x := by
  have hF : List.Forall₂ (fun m R => MSpec τ m U R) (l.map g) (l.map Rg) := by
    induction l with
    | nil => exact .nil
    | cons y ys ih => exact .cons (h y List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
  have := seqM_specL _ _ hF s hs
  exact ⟨this.le, this.loc, fun x => by rw [this.sem x]; simp⟩

end ZInQ.Compiler.Natural
