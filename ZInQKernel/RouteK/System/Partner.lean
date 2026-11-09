import ZInQKernel.RouteK.System.Selmer

/-!
# Route K: Lemma 1 (partner)

`docs/research/slot-k.md` §2.2, Lemma 1: if `r` is a glue prime (`c_r = 1`) with `[r/y] = 1` for
exactly one `y`, then forgetting `u_r, v_r` is a bijection from the solutions of `Σ(𝒞)` onto those of
`Σ(𝒞 ∖ r)`, with inverse `u_r = u_y`, `v_r = v_y`.

We first prove it for a whole family of partners at once: a configuration on `ι ⊕ R` in which every
`r ∈ R` is a glue prime whose only nonzero symbol is at `y r ∈ ι` (`partnerEquiv`). The single-prime
statement of the note is `eraseEquiv`. Both maps keep `a₀, a₁, b₀, b₁` and restrict `u, v`; so the
first-coordinate class `(a₀, a₁, u)` is preserved, the inverse extending `u` by `u_r = u_{y r}`.
-/

namespace ZInQ.RouteK

/-- An equivalence of finsets that is induced by a map `f` makes `f` a bijection between them. -/
theorem bijOn_of_equiv_coe {α β : Type*} {s : Finset α} {t : Finset β} {f : α → β} (E : s ≃ t)
    (hE : ∀ x, (E x).1 = f x.1) : Set.BijOn f s t := by
  refine ⟨fun x hx => ?_, fun x hx x' hx' hxx' => ?_, fun z hz => ?_⟩
  · rw [← hE ⟨x, hx⟩]; exact (E _).2
  · have : E ⟨x, hx⟩ = E ⟨x', hx'⟩ := Subtype.ext (by rw [hE, hE]; exact hxx')
    exact congrArg Subtype.val (E.injective this)
  · refine ⟨(E.symm ⟨z, hz⟩).1, (E.symm ⟨z, hz⟩).2, ?_⟩
    rw [← hE, Equiv.apply_symm_apply]

namespace Config

section family

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [Fintype R] [DecidableEq R]

/-- The restriction of a configuration on `ι ⊕ R` to `ι`. -/
def restrictLeft (𝒞 : Config (ι ⊕ R)) : Config ι where
  cls x := 𝒞.cls (.inl x)
  cls_mem _ := 𝒞.cls_mem _
  bit a b := 𝒞.bit (.inl a) (.inl b)
  recip _ _ h := 𝒞.recip _ _ (Sum.inl_injective.ne h)

/-- The hypotheses of Lemma 1 for the family `R`: every `r ∈ R` is a glue prime whose only nonzero
symbol `[r/z]` is at `z = y r`. -/
structure Partners (𝒞 : Config (ι ⊕ R)) (y : R → ι) : Prop where
  cls_eq_one : ∀ r, 𝒞.cls (.inr r) = 1
  bit_partner : ∀ r, 𝒞.bit (.inr r) (.inl (y r)) = 1
  bit_other : ∀ r z, z ≠ .inr r → z ≠ .inl (y r) → 𝒞.bit (.inr r) z = 0

/-- The inverse of Lemma 1: extend `u, v` by `u_r = u_{y r}`, `v_r = v_{y r}`. -/
def partnerExtend (y : R → ι) (σ : Unknowns ι) : Unknowns (ι ⊕ R) :=
  ⟨σ.a0, σ.a1, σ.b0, σ.b1, Sum.elim σ.u (σ.u ∘ y), Sum.elim σ.v (σ.v ∘ y)⟩

omit [Fintype ι] [DecidableEq ι] [Fintype R] [DecidableEq R] in
@[simp] theorem partnerExtend_comp_inl (y : R → ι) (σ : Unknowns ι) :
    (partnerExtend y σ).comp Sum.inl = σ := rfl

omit [Fintype ι] [DecidableEq ι] [Fintype R] [DecidableEq R] in
theorem partnerExtend_first (y : R → ι) (σ : Unknowns ι) :
    (partnerExtend y σ).first = (σ.a0, σ.a1, Sum.elim σ.u (σ.u ∘ y)) := rfl

variable {𝒞 : Config (ι ⊕ R)} {y : R → ι}

/-- `(Ku)_r = u_{y r} + u_r` at a partner `r`. -/
theorem Partners.monsky_inr (h : Partners 𝒞 y) (u : ι ⊕ R → ZMod 2) (r : R) :
    𝒞.monsky u (.inr r) = u (.inl (y r)) + u (.inr r) := by
  rw [monsky_eq_sum, Fintype.sum_eq_single (Sum.inl (y r))]
  · rw [𝒞.bit_symm_of_cls_one (h.cls_eq_one r) Sum.inl_ne_inr, h.bit_partner, one_mul]
  · intro z hz
    by_cases hzr : z = .inr r
    · subst hzr; rw [CharTwo.add_self_eq_zero, mul_zero]
    · rw [𝒞.bit_symm_of_cls_one (h.cls_eq_one r) hzr, h.bit_other r z hzr hz, zero_mul]

/-- At a symbol of `ι`, the partner terms of `(Ku)_x` vanish once `u_r = u_{y r}`. -/
theorem Partners.monsky_inl (h : Partners 𝒞 y) {u : ι ⊕ R → ZMod 2}
    (hu : ∀ r, u (.inr r) = u (.inl (y r))) (x : ι) :
    𝒞.monsky u (.inl x) = 𝒞.restrictLeft.monsky (u ∘ Sum.inl) x := by
  rw [monsky_eq_sum, monsky_eq_sum, Fintype.sum_sum_type]
  have : ∑ r : R, 𝒞.bit (.inr r) (.inl x) * (u (.inr r) + u (.inl x)) = 0 := by
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hx : x = y r
    · subst hx; rw [hu, CharTwo.add_self_eq_zero, mul_zero]
    · rw [h.bit_other r _ Sum.inl_ne_inr (fun e => hx (Sum.inl_injective e)), zero_mul]
  rw [this, add_zero]; rfl

omit [DecidableEq ι] [DecidableEq R] in
theorem Partners.prodClass_eq (h : Partners 𝒞 y) : 𝒞.prodClass = 𝒞.restrictLeft.prodClass := by
  rw [prodClass, Fintype.prod_sum_type]
  simp only [h.cls_eq_one, Finset.prod_const_one, mul_one]
  rfl

omit [DecidableEq ι] [DecidableEq R] in
theorem Partners.dot_lam (h : Partners 𝒞 y) (u : ι ⊕ R → ZMod 2) :
    dot 𝒞.lam u = dot 𝒞.restrictLeft.lam (u ∘ Sum.inl) := by
  rw [dot, Fintype.sum_sum_type]
  simp only [lam, h.cls_eq_one, lam8_one, zero_mul, Finset.sum_const_zero, add_zero]
  rfl

omit [DecidableEq ι] [DecidableEq R] in
theorem Partners.dot_mu (h : Partners 𝒞 y) (u : ι ⊕ R → ZMod 2) :
    dot 𝒞.mu u = dot 𝒞.restrictLeft.mu (u ∘ Sum.inl) := by
  rw [dot, Fintype.sum_sum_type]
  simp only [mu, h.cls_eq_one, mu8_one, zero_mul, Finset.sum_const_zero, add_zero]
  rfl

/-- Lemma 1, core: `σ` solves `Σ(𝒞)` iff `u_r = u_{y r}`, `v_r = v_{y r}` for every `r ∈ R` and the
restriction of `σ` solves `Σ(𝒞 ∖ R)`. -/
theorem Partners.isSol_iff (h : Partners 𝒞 y) (σ : Unknowns (ι ⊕ R)) :
    𝒞.IsSol σ ↔ ((∀ r, σ.u (.inr r) = σ.u (.inl (y r))) ∧ (∀ r, σ.v (.inr r) = σ.v (.inl (y r))))
      ∧ 𝒞.restrictLeft.IsSol (σ.comp Sum.inl) := by
  have hlr : ∀ r, 𝒞.lam (.inr r) = 0 := fun r => by simp [lam, h.cls_eq_one]
  have hmr : ∀ r, 𝒞.mu (.inr r) = 0 := fun r => by simp [mu, h.cls_eq_one]
  have key : ∀ a b : ZMod 2, a + b = 0 ↔ b = a := by decide
  have hE1r : ∀ r, 𝒞.E1 σ (.inr r) ↔ σ.u (.inr r) = σ.u (.inl (y r)) := fun r => by
    rw [E1, h.monsky_inr, hlr, hmr]; simp only [mul_zero, zero_mul, add_zero]; exact key _ _
  have hE2r : ∀ r, 𝒞.E2 σ (.inr r) ↔ σ.v (.inr r) = σ.v (.inl (y r)) := fun r => by
    rw [E2, h.monsky_inr, hlr, hmr]; simp only [mul_zero, zero_mul, add_zero, zero_add]
    exact key _ _
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hu := fun r => (hE1r r).1 (h1 _)
    have hv := fun r => (hE2r r).1 (h2 _)
    refine ⟨⟨hu, hv⟩, fun x => ?_, fun x => ?_, h3, ?_⟩
    · have := h1 (.inl x); rwa [E1, h.monsky_inl hu] at this
    · have := h2 (.inl x); rwa [E2, h.monsky_inl hv] at this
    · have := h4; rwa [D, h.prodClass_eq, h.dot_lam, h.dot_mu, h.dot_lam] at this
  · rintro ⟨⟨hu, hv⟩, h1, h2, h3, h4⟩
    refine ⟨?_, ?_, h3, ?_⟩
    · rintro (x | r)
      · have := h1 x; rwa [E1, h.monsky_inl hu]
      · exact (hE1r r).2 (hu r)
    · rintro (x | r)
      · have := h2 x; rwa [E2, h.monsky_inl hv]
      · exact (hE2r r).2 (hv r)
    · rwa [D, h.prodClass_eq, h.dot_lam, h.dot_mu, h.dot_lam]

theorem Partners.extend_mem (h : Partners 𝒞 y) {σ : Unknowns ι} (hσ : σ ∈ 𝒞.restrictLeft.sols) :
    partnerExtend y σ ∈ 𝒞.sols := by
  rw [mem_sols, h.isSol_iff]
  exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, (mem_sols _).1 hσ⟩

theorem Partners.comp_mem (h : Partners 𝒞 y) {σ : Unknowns (ι ⊕ R)} (hσ : σ ∈ 𝒞.sols) :
    σ.comp Sum.inl ∈ 𝒞.restrictLeft.sols := by
  rw [mem_sols]; exact ((h.isSol_iff σ).1 ((mem_sols _).1 hσ)).2

theorem Partners.extend_comp (h : Partners 𝒞 y) {σ : Unknowns (ι ⊕ R)} (hσ : σ ∈ 𝒞.sols) :
    partnerExtend y (σ.comp Sum.inl) = σ := by
  obtain ⟨⟨hu, hv⟩, -⟩ := (h.isSol_iff σ).1 ((mem_sols _).1 hσ)
  ext x
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases x with x | r
    · rfl
    · exact (hu r).symm
  · rcases x with x | r
    · rfl
    · exact (hv r).symm

/-- **Lemma 1** (family form): forgetting the partners is a bijection of solution sets. -/
def Partners.solsEquiv (h : Partners 𝒞 y) : 𝒞.sols ≃ 𝒞.restrictLeft.sols where
  toFun σ := ⟨σ.1.comp Sum.inl, h.comp_mem σ.2⟩
  invFun σ := ⟨partnerExtend y σ.1, h.extend_mem σ.2⟩
  left_inv σ := Subtype.ext (h.extend_comp σ.2)
  right_inv _ := rfl

@[simp] theorem Partners.solsEquiv_apply (h : Partners 𝒞 y) (σ : 𝒞.sols) :
    (h.solsEquiv σ).1 = σ.1.comp Sum.inl := rfl

@[simp] theorem Partners.solsEquiv_symm_apply (h : Partners 𝒞 y) (σ : 𝒞.restrictLeft.sols) :
    (h.solsEquiv.symm σ).1 = partnerExtend y σ.1 := rfl

theorem Partners.bijOn (h : Partners 𝒞 y) :
    Set.BijOn (fun σ : Unknowns (ι ⊕ R) => σ.comp Sum.inl) (𝒞.sols : Set (Unknowns (ι ⊕ R)))
      (𝒞.restrictLeft.sols : Set (Unknowns ι)) :=
  Set.InvOn.bijOn (f' := partnerExtend y) ⟨fun _ hσ => h.extend_comp hσ, fun _ _ => rfl⟩
    (fun _ hσ => h.comp_mem hσ) (fun _ hσ => h.extend_mem hσ)

theorem Partners.card_sols (h : Partners 𝒞 y) : 𝒞.sols.card = 𝒞.restrictLeft.sols.card :=
  Finset.card_eq_of_equiv h.solsEquiv

end family

section single

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The configuration `𝒞 ∖ r` on the remaining symbols. -/
def erase (𝒞 : Config ι) (r : ι) : Config {x // x ≠ r} where
  cls x := 𝒞.cls x
  cls_mem _ := 𝒞.cls_mem _
  bit x y := 𝒞.bit x y
  recip _ _ h := 𝒞.recip _ _ (fun e => h (Subtype.ext e))

/-- `ι ≃ {x // x ≠ r} ⊕ Unit`, sending `r` to the right summand. -/
def sumUnitEquiv (r : ι) : {x // x ≠ r} ⊕ Unit ≃ ι where
  toFun := Sum.elim Subtype.val fun _ => r
  invFun x := if h : x = r then .inr () else .inl ⟨x, h⟩
  left_inv := by
    rintro (x | u)
    · simp [x.2]
    · simp
  right_inv x := by
    by_cases h : x = r
    · simp [h]
    · simp [h]

/-- The hypotheses of Lemma 1 (partner): `r` is a glue prime (`c_r = 1`) and `[r/z] = 1` for exactly
one `z ≠ r`, namely `z = y`. -/
structure Partner (𝒞 : Config ι) (r y : ι) : Prop where
  ne : y ≠ r
  cls_eq_one : 𝒞.cls r = 1
  bit_partner : 𝒞.bit r y = 1
  bit_other : ∀ z, z ≠ r → z ≠ y → 𝒞.bit r z = 0

variable {𝒞 : Config ι} {r y : ι}

omit [Fintype ι] in
theorem Partner.partners (h : 𝒞.Partner r y) :
    Partners (𝒞.reindex (sumUnitEquiv r)) (fun _ => ⟨y, h.ne⟩) where
  cls_eq_one _ := h.cls_eq_one
  bit_partner _ := h.bit_partner
  bit_other := by
    rintro _ (z | ⟨⟩) hz hz'
    · exact h.bit_other z z.2 (fun e => hz' (congrArg Sum.inl (Subtype.ext e)))
    · exact absurd rfl hz

/-- **Lemma 1** (partner), the rows: `σ` solves `Σ(𝒞)` iff `u_r = u_y`, `v_r = v_y` and the
restriction of `σ` solves `Σ(𝒞 ∖ r)`. -/
theorem Partner.isSol_iff (h : 𝒞.Partner r y) (σ : Unknowns ι) :
    𝒞.IsSol σ ↔ (σ.u r = σ.u y ∧ σ.v r = σ.v y) ∧ (𝒞.erase r).IsSol (σ.comp Subtype.val) := by
  rw [← 𝒞.isSol_reindex_comp (sumUnitEquiv r), h.partners.isSol_iff]
  exact and_congr (and_congr ⟨fun H => H (), fun H _ => H⟩ ⟨fun H => H (), fun H _ => H⟩) Iff.rfl

/-- **Lemma 1** (partner): forgetting `u_r, v_r` is a bijection from the solutions of `Σ(𝒞)` onto
those of `Σ(𝒞 ∖ r)`. -/
def Partner.solsEquiv (h : 𝒞.Partner r y) : 𝒞.sols ≃ (𝒞.erase r).sols :=
  (𝒞.solsReindexEquiv (sumUnitEquiv r)).symm.trans h.partners.solsEquiv

@[simp] theorem Partner.solsEquiv_apply (h : 𝒞.Partner r y) (σ : 𝒞.sols) :
    (h.solsEquiv σ).1 = σ.1.comp Subtype.val := rfl

/-- The inverse keeps `a₀, a₁, b₀, b₁` and `u, v` away from `r`, and sets `u_r = u_y`, `v_r = v_y`. -/
theorem Partner.solsEquiv_symm_apply (h : 𝒞.Partner r y) (σ : (𝒞.erase r).sols) :
    (h.solsEquiv.symm σ).1.a0 = σ.1.a0 ∧ (h.solsEquiv.symm σ).1.a1 = σ.1.a1 ∧
    (h.solsEquiv.symm σ).1.b0 = σ.1.b0 ∧ (h.solsEquiv.symm σ).1.b1 = σ.1.b1 ∧
    (h.solsEquiv.symm σ).1.u r = σ.1.u ⟨y, h.ne⟩ ∧ (h.solsEquiv.symm σ).1.v r = σ.1.v ⟨y, h.ne⟩ ∧
    (∀ x (hx : x ≠ r), (h.solsEquiv.symm σ).1.u x = σ.1.u ⟨x, hx⟩ ∧
      (h.solsEquiv.symm σ).1.v x = σ.1.v ⟨x, hx⟩) := by
  have e : (h.solsEquiv.symm σ).1 =
      (partnerExtend (fun _ => ⟨y, h.ne⟩) σ.1).comp (sumUnitEquiv r).symm := rfl
  rw [e]
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, fun x hx => ⟨?_, ?_⟩⟩
  · simp [Unknowns.comp, partnerExtend, sumUnitEquiv]
  · simp [Unknowns.comp, partnerExtend, sumUnitEquiv]
  · simp [Unknowns.comp, partnerExtend, sumUnitEquiv, hx]
  · simp [Unknowns.comp, partnerExtend, sumUnitEquiv, hx]

theorem Partner.bijOn (h : 𝒞.Partner r y) :
    Set.BijOn (fun σ : Unknowns ι => σ.comp Subtype.val) (𝒞.sols : Set (Unknowns ι))
      ((𝒞.erase r).sols : Set (Unknowns {x // x ≠ r})) :=
  bijOn_of_equiv_coe h.solsEquiv fun _ => rfl

theorem Partner.card_sols (h : 𝒞.Partner r y) : 𝒞.sols.card = (𝒞.erase r).sols.card :=
  Finset.card_eq_of_equiv h.solsEquiv

end single

end Config

end ZInQ.RouteK
