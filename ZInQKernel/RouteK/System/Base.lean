import ZInQKernel.RouteK.System.Selmer

/-!
# Route K: Lemma 3 (the base configuration)

`docs/research/slot-k.md` §2.3, Lemma 3: let `𝒞₀` be a configuration on `{p*, q₀}` with
`c_{p*} = 7`, `c_{q₀} = 3` and `x = [q₀/p*]`. Then `Σ(𝒞₀)` has exactly 8 solutions (dimension 3),
and for each `a₀` it contains

```
σ₀ :  u = (1, 0),  v = (a₀ + x, a₀ + x + 1),  a₁ = 0,  b₀ = a₀,  b₁ = 0,
```

whose first coordinate is the class `(−1)^{a₀} p*`.

The index type is `Fin 2` with `p* = 0` and `q₀ = 1`; `base_card_sols'` and `base_exists_first'`
state the lemma for any two-element index type. The solutions are described explicitly
(`base_isSol_iff`): `a₀, u_{p*}, u_{q₀}` are free and the rest is determined. The finite check behind
this is a `decide` over the nine bits involved (`base_isSol_iff`).
-/

namespace ZInQ.RouteK

namespace Config

theorem twoAdicRows_five {a1 b0 b1 lu mu lv : ZMod 2} :
    twoAdicRows 5 a1 b0 b1 lu mu lv ↔ a1 = 0 ∧ b1 = mu ∧ lv = lu := by
  simp only [twoAdicRows, (by decide : (5 : ZMod 8) ≠ 1), (by decide : (5 : ZMod 8) ≠ 3),
    ↓reduceIte]

variable (𝒞 : Config (Fin 2))

set_option synthInstance.maxSize 4096 in
/-- The solutions of `Σ(𝒞₀)`: `a₀, u_{p*}, u_{q₀}` are free, and with `w = u_{p*} + u_{q₀}`,
`v_{p*} = a₀ + xw`, `v_{q₀} = a₀ + (x + 1)w`, `a₁ = 0`, `b₀ = a₀`, `b₁ = u_{q₀}`. -/
theorem base_isSol_iff (h0 : 𝒞.cls 0 = 7) (h1 : 𝒞.cls 1 = 3) (σ : Unknowns (Fin 2)) :
    𝒞.IsSol σ ↔ σ.a1 = 0 ∧ σ.b0 = σ.a0 ∧ σ.b1 = σ.u 1 ∧
      σ.v 0 = σ.a0 + 𝒞.bit 1 0 * (σ.u 0 + σ.u 1) ∧
      σ.v 1 = σ.a0 + (𝒞.bit 1 0 + 1) * (σ.u 0 + σ.u 1) := by
  have hl0 : 𝒞.lam 0 = 1 := by rw [lam, h0]; decide
  have hl1 : 𝒞.lam 1 = 1 := by rw [lam, h1]; decide
  have hm0 : 𝒞.mu 0 = 0 := by rw [mu, h0]; decide
  have hm1 : 𝒞.mu 1 = 1 := by rw [mu, h1]; decide
  have hc : 𝒞.prodClass = 5 := by rw [prodClass, Fin.prod_univ_two, h0, h1]; decide
  have hb : 𝒞.bit 0 1 = 𝒞.bit 1 0 + 1 := by
    have := 𝒞.recip' (x := 0) (y := 1) (by decide)
    rw [hl0, hl1] at this
    linear_combination (norm := (ring_nf; reduce_mod_char)) this
  simp only [IsSol, E1, E2, D, Fin.forall_fin_two, monsky_eq_sum, Fin.sum_univ_two, dot, hc,
    twoAdicRows_five, hl0, hl1, hm0, hm1, hb, CharTwo.add_self_eq_zero, mul_zero, zero_add,
    add_zero, one_mul, mul_one, zero_mul]
  -- the finite check: nine bits
  generalize 𝒞.bit 1 0 = x
  generalize σ.a0 = a0
  generalize σ.a1 = a1
  generalize σ.b0 = b0
  generalize σ.b1 = b1
  generalize σ.u 0 = u0
  generalize σ.u 1 = u1
  generalize σ.v 0 = v0
  generalize σ.v 1 = v1
  revert x a0 a1 b0 b1 u0 u1 v0 v1
  decide

/-- The solutions of Lemma 3, parametrized by `(a₀, u_{p*}, u_{q₀})`. -/
def baseSol (x : ZMod 2) (t : ZMod 2 × ZMod 2 × ZMod 2) : Unknowns (Fin 2) :=
  ⟨t.1, 0, t.1, t.2.2, ![t.2.1, t.2.2],
    ![t.1 + x * (t.2.1 + t.2.2), t.1 + (x + 1) * (t.2.1 + t.2.2)]⟩

theorem baseSol_injective (x : ZMod 2) : Function.Injective (baseSol x) := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  simp only [baseSol, Unknowns.mk.injEq] at h
  obtain ⟨ha, -, -, -, hu, -⟩ := h
  have hb := congrFun hu 0
  have hc := congrFun hu 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hb hc
  rw [ha, hb, hc]

theorem base_sols_eq (h0 : 𝒞.cls 0 = 7) (h1 : 𝒞.cls 1 = 3) :
    𝒞.sols = Finset.univ.image (baseSol (𝒞.bit 1 0)) := by
  ext σ
  simp only [mem_sols, base_isSol_iff 𝒞 h0 h1, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨ha1, hb0, hb1, hv0, hv1⟩
    refine ⟨(σ.a0, σ.u 0, σ.u 1), ?_⟩
    ext i
    · rfl
    · exact ha1.symm
    · exact hb0.symm
    · exact hb1.symm
    · fin_cases i <;> rfl
    · fin_cases i
      · exact hv0.symm
      · exact hv1.symm
  · rintro ⟨t, rfl⟩
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Lemma 3**, dimension: `Σ(𝒞₀)` has exactly `8 = 2³` solutions. -/
theorem base_card_sols (h0 : 𝒞.cls 0 = 7) (h1 : 𝒞.cls 1 = 3) : 𝒞.sols.card = 8 := by
  rw [base_sols_eq 𝒞 h0 h1, Finset.card_image_of_injective _ (baseSol_injective _)]
  rfl

/-- The solution `σ₀` of Lemma 3. -/
def baseSol₀ (x a0 : ZMod 2) : Unknowns (Fin 2) :=
  ⟨a0, 0, a0, 0, ![1, 0], ![a0 + x, a0 + x + 1]⟩

/-- **Lemma 3**, the solution `σ₀`: for each `a₀`, `σ₀` solves `Σ(𝒞₀)`, where `x = [q₀/p*]`. -/
theorem baseSol₀_mem (h0 : 𝒞.cls 0 = 7) (h1 : 𝒞.cls 1 = 3) (a0 : ZMod 2) :
    baseSol₀ (𝒞.bit 1 0) a0 ∈ 𝒞.sols := by
  rw [mem_sols, base_isSol_iff 𝒞 h0 h1]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩ <;>
    simp only [baseSol₀, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    ring_nf

/-- **Lemma 3**, first coordinate: for each `a₀` there is a solution with first coordinate
`(a₀, 0, 𝟏_{p*})`, i.e. the class `(−1)^{a₀} p*`. -/
theorem base_exists_first (h0 : 𝒞.cls 0 = 7) (h1 : 𝒞.cls 1 = 3) (a0 : ZMod 2) :
    ∃ σ ∈ 𝒞.sols, σ.first = (a0, 0, ![1, 0]) :=
  ⟨_, baseSol₀_mem 𝒞 h0 h1 a0, rfl⟩

section twoElements

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p q : ι}

/-- An index type with exactly two elements `p ≠ q`, as `Fin 2` (`0 ↦ p`, `1 ↦ q`). -/
def finTwoEquiv (hpq : p ≠ q) (hall : ∀ z, z = p ∨ z = q) : Fin 2 ≃ ι where
  toFun i := if i = 0 then p else q
  invFun z := if z = p then 0 else 1
  left_inv i := by fin_cases i <;> simp [hpq.symm]
  right_inv z := by
    rcases hall z with rfl | rfl
    · simp
    · simp [hpq.symm]

/-- **Lemma 3** on any two-element configuration `{p*, q₀}`: `Σ(𝒞₀)` has 8 solutions. -/
theorem base_card_sols' (𝒞 : Config ι) (hpq : p ≠ q) (hall : ∀ z, z = p ∨ z = q)
    (hp : 𝒞.cls p = 7) (hq : 𝒞.cls q = 3) : 𝒞.sols.card = 8 := by
  rw [← 𝒞.card_sols_reindex (finTwoEquiv hpq hall)]
  exact base_card_sols _ (by simpa [finTwoEquiv] using hp) (by simpa [finTwoEquiv] using hq)

/-- **Lemma 3** on any two-element configuration `{p*, q₀}`: for each `a₀`, `Σ(𝒞₀)` has the
solution `σ₀` (`u = 𝟏_{p*}`, `v_{p*} = a₀ + [q₀/p*]`, `v_{q₀} = a₀ + [q₀/p*] + 1`, `a₁ = 0`,
`b₀ = a₀`, `b₁ = 0`). -/
theorem base_mem_sols' (𝒞 : Config ι) (hpq : p ≠ q) (hall : ∀ z, z = p ∨ z = q)
    (hp : 𝒞.cls p = 7) (hq : 𝒞.cls q = 3) (a0 : ZMod 2) :
    (⟨a0, 0, a0, 0, fun z => if z = p then 1 else 0,
      fun z => if z = p then a0 + 𝒞.bit q p else a0 + 𝒞.bit q p + 1⟩ : Unknowns ι) ∈ 𝒞.sols := by
  set e := finTwoEquiv hpq hall
  have hmem := baseSol₀_mem (𝒞.reindex e) (by simpa [e, finTwoEquiv] using hp)
    (by simpa [e, finTwoEquiv] using hq) a0
  have := ((𝒞.solsReindexEquiv e) ⟨_, hmem⟩).2
  convert this using 1
  have he : ∀ z, e.symm z = if z = p then 0 else 1 := fun _ => rfl
  ext z
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [solsReindexEquiv, Equiv.coe_fn_mk, Unknowns.comp, Function.comp_apply, he,
      baseSol₀]
    split_ifs <;> rfl
  · simp only [solsReindexEquiv, Equiv.coe_fn_mk, Unknowns.comp, Function.comp_apply, he,
      baseSol₀, reindex_bit]
    have e0 : e 0 = p := rfl
    have e1 : e 1 = q := by simp [e, finTwoEquiv]
    split_ifs <;> simp [e0, e1]

/-- **Lemma 3**, first coordinate, on any two-element configuration. -/
theorem base_exists_first' (𝒞 : Config ι) (hpq : p ≠ q) (hall : ∀ z, z = p ∨ z = q)
    (hp : 𝒞.cls p = 7) (hq : 𝒞.cls q = 3) (a0 : ZMod 2) :
    ∃ σ ∈ 𝒞.sols, σ.first = (a0, 0, fun z => if z = p then 1 else 0) :=
  ⟨_, base_mem_sols' 𝒞 hpq hall hp hq a0, rfl⟩

end twoElements

end Config

end ZInQ.RouteK
