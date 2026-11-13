import ZInQKernel.RouteK.System.Config

/-!
# Route K: the Selmer system `Σ(𝒞)`

The unknowns are `a₀, a₁, b₀, b₁ ∈ 𝔽₂` and `u, v ∈ 𝔽₂^S` (`docs/research/slot-k.md` §2.1). With
Monsky's matrix `(Ku)_x = Σ_{y ≠ x} [y/x](u_y + u_x)` the equations are

```
(E1_x)  (Ku)_x + λ_x v_x = a₀λ_x + a₁μ_x
(E2_x)  μ_x u_x + (Kv)_x + λ_x v_x = b₀λ_x + b₁μ_x
(R)     a₀ = b₀
(D)     the two 2-adic rows for c(𝒞) (`twoAdicRows`).
```

A solution stands for the pair of classes `a = (−1)^{a₀}2^{a₁}Π x^{u_x}`,
`b = (−1)^{b₀}2^{b₁}Π x^{v_x}`; its first-coordinate class is recorded by `(a₀, a₁, u)`.
-/

namespace ZInQ.RouteK

/-- The unknowns `(a₀, a₁, b₀, b₁, u, v)` of the Selmer system on the index type `ι`. -/
@[ext]
structure Unknowns (ι : Type*) where
  a0 : ZMod 2
  a1 : ZMod 2
  b0 : ZMod 2
  b1 : ZMod 2
  u : ι → ZMod 2
  v : ι → ZMod 2

namespace Unknowns

variable {ι : Type*}

/-- `Unknowns ι` as a product type. -/
def equivProd : Unknowns ι ≃ ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2 × (ι → ZMod 2) × (ι → ZMod 2) where
  toFun σ := (σ.a0, σ.a1, σ.b0, σ.b1, σ.u, σ.v)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype ι] [DecidableEq ι] : Fintype (Unknowns ι) := Fintype.ofEquiv _ equivProd.symm

instance [Fintype ι] [DecidableEq ι] : DecidableEq (Unknowns ι) := fun σ τ =>
  decidable_of_iff (σ.a0 = τ.a0 ∧ σ.a1 = τ.a1 ∧ σ.b0 = τ.b0 ∧ σ.b1 = τ.b1 ∧ σ.u = τ.u ∧ σ.v = τ.v)
    ⟨fun ⟨h1, h2, h3, h4, h5, h6⟩ => Unknowns.ext h1 h2 h3 h4 h5 h6, fun h => by subst h; simp⟩

/-- The first-coordinate class `(a₀, a₁, u)`, standing for `a = (−1)^{a₀}2^{a₁}Π x^{u_x}`. -/
def first (σ : Unknowns ι) : ZMod 2 × ZMod 2 × (ι → ZMod 2) := (σ.a0, σ.a1, σ.u)

/-- Reindexing the unknowns along a map `e : κ → ι`. -/
def comp {κ : Type*} (σ : Unknowns ι) (e : κ → ι) : Unknowns κ :=
  ⟨σ.a0, σ.a1, σ.b0, σ.b1, σ.u ∘ e, σ.v ∘ e⟩

end Unknowns

/-- The 2-adic rows `(D)` for the class `c = c(𝒞)`, in terms of `a₁, b₀, b₁` and
`lu = λ·u`, `mu = μ·u`, `lv = λ·v`. For an even `c` (which never occurs) there are no solutions. -/
def twoAdicRows (c : ZMod 8) (a1 b0 b1 lu mu lv : ZMod 2) : Prop :=
  if c = 1 then a1 = 0 ∧ mu = 0 ∧ lv = lu
  else if c = 3 then a1 = 0 ∧ b0 = lv ∧ b1 = mu
  else if c = 5 then a1 = 0 ∧ b1 = mu ∧ lv = lu
  else if c = 7 then a1 = 0 ∧ mu = 0 ∧ b0 = lv
  else False

instance (c : ZMod 8) (a1 b0 b1 lu mu lv : ZMod 2) :
    Decidable (twoAdicRows c a1 b0 b1 lu mu lv) := by
  unfold twoAdicRows; infer_instance

/-- Every row `(D)` contains `a₁ = 0`. -/
theorem twoAdicRows_a1 {c : ZMod 8} {a1 b0 b1 lu mu lv : ZMod 2}
    (h : twoAdicRows c a1 b0 b1 lu mu lv) : a1 = 0 := by
  unfold twoAdicRows at h
  split_ifs at h <;> exact h.1

/-- The dot product `f·g = Σ_x f_x g_x` over `𝔽₂`. -/
def dot {ι : Type*} [Fintype ι] (f g : ι → ZMod 2) : ZMod 2 := ∑ x, f x * g x

namespace Config

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (𝒞 : Config ι)

/-- Monsky's matrix: `(Ku)_x = Σ_{y ≠ x} [y/x](u_y + u_x)`. -/
def monsky (u : ι → ZMod 2) (x : ι) : ZMod 2 :=
  ∑ y ∈ Finset.univ.erase x, 𝒞.bit y x * (u y + u x)

/-- The row `E1_x`: `(Ku)_x + λ_x v_x = a₀λ_x + a₁μ_x`. -/
def E1 (σ : Unknowns ι) (x : ι) : Prop :=
  𝒞.monsky σ.u x + 𝒞.lam x * σ.v x = σ.a0 * 𝒞.lam x + σ.a1 * 𝒞.mu x

/-- The row `E2_x`: `μ_x u_x + (Kv)_x + λ_x v_x = b₀λ_x + b₁μ_x`. -/
def E2 (σ : Unknowns ι) (x : ι) : Prop :=
  𝒞.mu x * σ.u x + 𝒞.monsky σ.v x + 𝒞.lam x * σ.v x = σ.b0 * 𝒞.lam x + σ.b1 * 𝒞.mu x

/-- The 2-adic rows `(D)` of `Σ(𝒞)`. -/
def D (σ : Unknowns ι) : Prop :=
  twoAdicRows 𝒞.prodClass σ.a1 σ.b0 σ.b1 (dot 𝒞.lam σ.u) (dot 𝒞.mu σ.u) (dot 𝒞.lam σ.v)

/-- `σ` solves the Selmer system `Σ(𝒞)`: rows `E1`, `E2` at every symbol, `(R)` and `(D)`. -/
def IsSol (σ : Unknowns ι) : Prop :=
  (∀ x, 𝒞.E1 σ x) ∧ (∀ x, 𝒞.E2 σ x) ∧ σ.a0 = σ.b0 ∧ 𝒞.D σ

instance : DecidablePred 𝒞.IsSol := fun σ => by
  unfold IsSol E1 E2 D; infer_instance

/-- The solution set of `Σ(𝒞)`. -/
def sols : Finset (Unknowns ι) := Finset.univ.filter 𝒞.IsSol

@[simp] theorem mem_sols {σ : Unknowns ι} : σ ∈ 𝒞.sols ↔ 𝒞.IsSol σ := by
  simp [sols]

/-- The diagonal term of `K` vanishes, so `(Ku)_x` is a sum over all `y`. -/
theorem monsky_eq_sum (u : ι → ZMod 2) (x : ι) :
    𝒞.monsky u x = ∑ y, 𝒞.bit y x * (u y + u x) :=
  Finset.sum_erase _ (by rw [CharTwo.add_self_eq_zero, mul_zero])

theorem IsSol.a1_eq_zero {σ : Unknowns ι} (h : 𝒞.IsSol σ) : σ.a1 = 0 :=
  twoAdicRows_a1 h.2.2.2

/-- The system depends only on the classes and the off-diagonal symbols. -/
theorem isSol_congr {𝒞' : Config ι} (hc : ∀ x, 𝒞.cls x = 𝒞'.cls x)
    (hb : ∀ x y, x ≠ y → 𝒞.bit x y = 𝒞'.bit x y) (σ : Unknowns ι) :
    𝒞.IsSol σ ↔ 𝒞'.IsSol σ := by
  have hK : ∀ (u : ι → ZMod 2) x, 𝒞.monsky u x = 𝒞'.monsky u x := fun u x =>
    Finset.sum_congr rfl fun y hy => by rw [hb y x (Finset.ne_of_mem_erase hy)]
  have hl : 𝒞.lam = 𝒞'.lam := funext fun x => by simp [lam, hc x]
  have hm : 𝒞.mu = 𝒞'.mu := funext fun x => by simp [mu, hc x]
  have hp : 𝒞.prodClass = 𝒞'.prodClass := Finset.prod_congr rfl fun x _ => hc x
  simp only [IsSol, E1, E2, D, hK, hl, hm, hp]

theorem sols_congr {𝒞' : Config ι} (hc : ∀ x, 𝒞.cls x = 𝒞'.cls x)
    (hb : ∀ x y, x ≠ y → 𝒞.bit x y = 𝒞'.bit x y) : 𝒞.sols = 𝒞'.sols := by
  ext σ; simp only [mem_sols]; exact 𝒞.isSol_congr hc hb σ

section reindex

variable {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)

theorem isSol_reindex_comp (σ : Unknowns ι) : (𝒞.reindex e).IsSol (σ.comp e) ↔ 𝒞.IsSol σ := by
  have hK : ∀ (u : ι → ZMod 2) x, (𝒞.reindex e).monsky (u ∘ e) x = 𝒞.monsky u (e x) := by
    intro u x
    rw [monsky_eq_sum, monsky_eq_sum]
    exact e.sum_comp (fun y => 𝒞.bit y (e x) * (u y + u (e x)))
  have hdot : ∀ (f g : ι → ZMod 2), dot (f ∘ e) (g ∘ e) = dot f g := fun f g =>
    e.sum_comp (fun y => f y * g y)
  have hl : (𝒞.reindex e).lam = 𝒞.lam ∘ e := rfl
  have hm : (𝒞.reindex e).mu = 𝒞.mu ∘ e := rfl
  simp only [IsSol, E1, E2, D, Unknowns.comp, hK, hl, hm, hdot, prodClass_reindex]
  simp only [Function.comp_apply]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun x => by simpa using h1 (e.symm x), fun x => by simpa using h2 (e.symm x), h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨fun x => h1 (e x), fun x => h2 (e x), h3, h4⟩

/-- Reindexing along `e : κ ≃ ι` identifies the solution sets, by `σ ↦ σ ∘ e`. -/
def solsReindexEquiv : (𝒞.reindex e).sols ≃ 𝒞.sols where
  toFun σ := ⟨σ.1.comp e.symm, by
    have := (𝒞.isSol_reindex_comp e (σ.1.comp e.symm)).1
    rw [mem_sols]; apply this
    have h : (σ.1.comp e.symm).comp e = σ.1 := by
      ext <;> simp [Unknowns.comp]
    rw [h]; exact (mem_sols _).1 σ.2⟩
  invFun σ := ⟨σ.1.comp e, by rw [mem_sols, isSol_reindex_comp]; exact (mem_sols _).1 σ.2⟩
  left_inv σ := by ext <;> simp [Unknowns.comp]
  right_inv σ := by ext <;> simp [Unknowns.comp]

@[simp] theorem solsReindexEquiv_symm_apply (σ : 𝒞.sols) :
    ((𝒞.solsReindexEquiv e).symm σ).1 = σ.1.comp e := rfl

theorem card_sols_reindex : (𝒞.reindex e).sols.card = 𝒞.sols.card := by
  rw [← Fintype.card_coe, ← Fintype.card_coe]
  exact Fintype.card_congr (𝒞.solsReindexEquiv e)

/-- Two configurations that match through `e : κ ≃ ι` on the classes and on the off-diagonal
symbols have corresponding solution sets, by `σ ↦ σ ∘ e⁻¹`. -/
def solsEquivOfIso {𝒞' : Config κ} (hc : ∀ x, 𝒞'.cls x = 𝒞.cls (e x))
    (hb : ∀ x y, x ≠ y → 𝒞'.bit x y = 𝒞.bit (e x) (e y)) : 𝒞'.sols ≃ 𝒞.sols :=
  (Equiv.subtypeEquivRight fun σ => by
    rw [𝒞'.sols_congr (𝒞' := 𝒞.reindex e) hc hb]).trans (𝒞.solsReindexEquiv e)

@[simp] theorem solsEquivOfIso_apply {𝒞' : Config κ} (hc : ∀ x, 𝒞'.cls x = 𝒞.cls (e x))
    (hb : ∀ x y, x ≠ y → 𝒞'.bit x y = 𝒞.bit (e x) (e y)) (σ : 𝒞'.sols) :
    (𝒞.solsEquivOfIso e hc hb σ).1 = σ.1.comp e.symm := rfl

@[simp] theorem solsEquivOfIso_symm_apply {𝒞' : Config κ} (hc : ∀ x, 𝒞'.cls x = 𝒞.cls (e x))
    (hb : ∀ x y, x ≠ y → 𝒞'.bit x y = 𝒞.bit (e x) (e y)) (σ : 𝒞.sols) :
    ((𝒞.solsEquivOfIso e hc hb).symm σ).1 = σ.1.comp e := rfl

theorem card_sols_of_iso {𝒞' : Config κ} (hc : ∀ x, 𝒞'.cls x = 𝒞.cls (e x))
    (hb : ∀ x y, x ≠ y → 𝒞'.bit x y = 𝒞.bit (e x) (e y)) : 𝒞'.sols.card = 𝒞.sols.card :=
  Finset.card_eq_of_equiv (𝒞.solsEquivOfIso e hc hb)

end reindex

end Config

end ZInQ.RouteK
