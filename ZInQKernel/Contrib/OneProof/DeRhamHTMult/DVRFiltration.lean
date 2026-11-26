import Mathlib

/-! # The filtration `ϖ^i R` of the fraction ring of a discrete valuation ring

For a discrete valuation ring `R` with fraction ring `B` and a uniformizer `ϖ` (`u ∈ Bˣ` its
image), `filU u i = ϖ^i R ⊆ B` (`i ∈ ℤ`) is a decreasing, exhaustive, separated filtration by
`K`-subspaces (`K → R` any algebra). A ring map `θ : R → C` with kernel `(ϖ)` gives `K`-linear
maps `gU θ i : ϖ^i R → C`, `ϖ^i y ↦ θ(y)`, with kernel `ϖ^{i+1} R`. If an endomorphism `τ` of `B`
preserves `R` (as `τR`), satisfies `τ(u^i) = w_i u^i` and `θ ∘ τR = τC ∘ θ`, then `τ` preserves
each `ϖ^i R` and `gU θ i ∘ τ = w_i • τC ∘ gU θ i`.

Neither the filtration nor the kernels depend on the uniformizer (`filU_eq_of_associated`).
-/

set_option autoImplicit false

namespace DeRhamHTMult

open Module

noncomputable section

section DVRFil

variable {K R B : Type*} [Field K] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing B] [Algebra R B] [IsFractionRing R B] [Algebra K B]
  (κ : K →+* R) (hκ : ∀ c, algebraMap K B c = algebraMap R B (κ c))

/-- `ϖ^i R ⊆ B`, with `u ∈ Bˣ` the image of `ϖ`. -/
def filU (u : Bˣ) (i : ℤ) : Submodule K B where
  carrier := {x | ∃ y : R, x = ↑(u ^ i) * algebraMap R B y}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨y, rfl⟩ ⟨y', rfl⟩
    exact ⟨y + y', by rw [map_add, mul_add]⟩
  smul_mem' := by
    rintro c _ ⟨y, rfl⟩
    refine ⟨κ c * y, ?_⟩
    rw [Algebra.smul_def, map_mul, hκ]
    ring

theorem mem_filU (u : Bˣ) (i : ℤ) (x : B) :
    x ∈ filU κ hκ u i ↔ ∃ y : R, x = ↑(u ^ i) * algebraMap R B y := Iff.rfl

variable {ϖ : R} {u : Bˣ}

theorem algebraMap_injective' : Function.Injective (algebraMap R B) :=
  IsFractionRing.injective R B

theorem val_zpow_natCast (hu : (u : B) = algebraMap R B ϖ) (k : ℕ) :
    (↑(u ^ (k : ℤ)) : B) = algebraMap R B (ϖ ^ k) := by
  rw [zpow_natCast, Units.val_pow_eq_pow_val, hu, map_pow]

theorem filU_anti (hu : (u : B) = algebraMap R B ϖ) : Antitone (filU κ hκ u) := by
  intro i j hij x hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨k, hk⟩ : ∃ k : ℕ, j = i + k := ⟨(j - i).toNat, by omega⟩
  refine ⟨ϖ ^ k * y, ?_⟩
  rw [hk, zpow_add, Units.val_mul, val_zpow_natCast hu, map_mul]
  ring

theorem eq_of_filU (i : ℤ) {y y' : R}
    (h : (↑(u ^ i) : B) * algebraMap R B y = ↑(u ^ i) * algebraMap R B y') : y = y' :=
  algebraMap_injective' (B := B) ((Units.mul_right_inj _).mp h)

theorem filU_exhaustive (hu : (u : B) = algebraMap R B ϖ) (hϖ : Irreducible ϖ) (x : B) :
    ∃ i, x ∈ filU κ hκ u i := by
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
  have hs0 : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
  refine ⟨-(m : ℤ), a * ↑v⁻¹, ?_⟩
  have hspec := IsLocalization.mk'_spec B a s
  have hum : (↑(u ^ (m : ℤ)) : B) * ↑(u ^ (-(m : ℤ))) = 1 := by
    rw [← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one]
  have hvv : algebraMap R B (↑v⁻¹ : R) * algebraMap R B (v : R) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  set z := IsLocalization.mk' B a s
  have e : algebraMap R B (s : R) = algebraMap R B (v : R) * ↑(u ^ (m : ℤ)) := by
    rw [hv, map_mul, val_zpow_natCast hu]
  rw [e] at hspec
  calc z = z * (algebraMap R B (v : R) * ↑(u ^ (m : ℤ))) *
        (↑(u ^ (-(m : ℤ))) * algebraMap R B (↑v⁻¹ : R)) := by
          rw [show z * (algebraMap R B (v : R) * ↑(u ^ (m : ℤ))) *
              (↑(u ^ (-(m : ℤ))) * algebraMap R B (↑v⁻¹ : R)) =
              z * ((algebraMap R B (↑v⁻¹ : R) * algebraMap R B (v : R)) *
                ((↑(u ^ (m : ℤ)) : B) * ↑(u ^ (-(m : ℤ))))) by ring, hvv, hum, mul_one, mul_one]
    _ = ↑(u ^ (-(m : ℤ))) * algebraMap R B (a * ↑v⁻¹) := by
          rw [hspec, map_mul]; ring

theorem filU_separated (hu : (u : B) = algebraMap R B ϖ) (hϖ : Irreducible ϖ) (x : B)
    (hx : ∀ i, x ∈ filU κ hκ u i) : x = 0 := by
  by_contra hne
  obtain ⟨y, hy⟩ := hx 0
  rw [zpow_zero, Units.val_one, one_mul] at hy
  have hy0 : y ≠ 0 := by rintro rfl; exact hne (by rw [hy, map_zero])
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  obtain ⟨y', hy'⟩ := hx ((m : ℤ) + 1)
  have e : algebraMap R B ((v : R) * ϖ ^ m) = algebraMap R B (ϖ ^ (m + 1) * y') := by
    rw [← hv, ← hy, hy', show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring,
      val_zpow_natCast hu, map_mul]
  have e2 := algebraMap_injective' (B := B) e
  have hϖ0 : ϖ ^ m ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have e3 : (v : R) = ϖ * y' := by
    apply mul_right_cancel₀ hϖ0
    rw [e2]; ring
  exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (e3 ▸ v.isUnit))

/-- Two uniformizers give the same filtration. -/
theorem filU_eq_of_associated {ϖ' : R} {u' : Bˣ} (hu : (u : B) = algebraMap R B ϖ)
    (hu' : (u' : B) = algebraMap R B ϖ') (h : Associated ϖ ϖ') (i : ℤ) :
    filU κ hκ u i = filU κ hκ u' i := by
  obtain ⟨e, he⟩ := h
  -- `u' = u · e`
  let eB : Bˣ := Units.map (algebraMap R B).toMonoidHom e
  have hu'e : u' = u * eB := Units.ext (by
    rw [Units.val_mul, hu', hu, ← he, map_mul]; rfl)
  have key : ∀ (a : Bˣ) (c : Rˣ) (i : ℤ) (x : B), x ∈ filU κ hκ a i →
      x ∈ filU κ hκ (a * Units.map (algebraMap R B).toMonoidHom c) i := by
    intro a c i x hx
    obtain ⟨y, rfl⟩ := hx
    refine ⟨↑(c ^ (-i)) * y, ?_⟩
    rw [mul_zpow, Units.val_mul, ← map_zpow, map_mul]
    have : (↑(Units.map (algebraMap R B).toMonoidHom (c ^ i)) : B) *
        algebraMap R B (↑(c ^ (-i)) : R) = 1 := by
      rw [Units.coe_map]
      change algebraMap R B (↑(c ^ i) : R) * algebraMap R B (↑(c ^ (-i)) : R) = 1
      rw [← map_mul, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one,
        map_one]
    linear_combination (↑(a ^ i) : B) * algebraMap R B y * this.symm
  apply le_antisymm
  · intro x hx; rw [hu'e]; exact key u e i x hx
  · intro x hx
    have : u = u' * Units.map (algebraMap R B).toMonoidHom e⁻¹ := by
      rw [hu'e, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    rw [this]; exact key u' e⁻¹ i x hx

variable {C : Type*} [CommRing C] [Algebra K C] (θ : R →+* C)

/-- The coordinate `y` of `x = ϖ^i y ∈ ϖ^i R`. -/
def coordU (i : ℤ) (x : filU κ hκ u i) : R := Classical.choose x.2

theorem coordU_spec (i : ℤ) (x : filU κ hκ u i) :
    (x : B) = ↑(u ^ i) * algebraMap R B (coordU κ hκ i x) := Classical.choose_spec x.2

theorem coordU_eq (i : ℤ) (x : filU κ hκ u i) {y : R} (hy : (x : B) = ↑(u ^ i) * algebraMap R B y) :
    coordU κ hκ i x = y :=
  eq_of_filU i ((coordU_spec κ hκ i x).symm.trans hy)

/-- `ϖ^i y ↦ θ(y)`. -/
def gU (hθK : ∀ c, θ (κ c) = algebraMap K C c) (i : ℤ) : filU κ hκ u i →ₗ[K] C where
  toFun x := θ (coordU κ hκ i x)
  map_add' x x' := by
    rw [coordU_eq κ hκ i (x + x') (y := coordU κ hκ i x + coordU κ hκ i x') (by
      rw [Submodule.coe_add, coordU_spec κ hκ i x, coordU_spec κ hκ i x', map_add,
        mul_add]), map_add]
  map_smul' c x := by
    rw [coordU_eq κ hκ i (c • x) (y := κ c * coordU κ hκ i x) (by
      rw [Submodule.coe_smul, coordU_spec κ hκ i x, Algebra.smul_def, map_mul, hκ]; ring),
      map_mul, hθK, RingHom.id_apply, Algebra.smul_def]

theorem gU_apply (hθK : ∀ c, θ (κ c) = algebraMap K C c) (i : ℤ) (x : filU κ hκ u i)
    {y : R} (hy : (x : B) = ↑(u ^ i) * algebraMap R B y) : gU κ hκ θ hθK i x = θ y := by
  change θ (coordU κ hκ i x) = θ y
  rw [coordU_eq κ hκ i x hy]

theorem gU_eq_zero_iff (hu : (u : B) = algebraMap R B ϖ)
    (hθK : ∀ c, θ (κ c) = algebraMap K C c)
    (hker : RingHom.ker θ = Ideal.span {ϖ}) (i : ℤ) (x : filU κ hκ u i) :
    gU κ hκ θ hθK i x = 0 ↔ (x : B) ∈ filU κ hκ u (i + 1) := by
  have hx := coordU_spec κ hκ i x
  rw [gU_apply κ hκ θ hθK i x hx]
  constructor
  · intro h0
    have : coordU κ hκ i x ∈ Ideal.span {ϖ} := by rw [← hker]; exact h0
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp this
    refine ⟨z, ?_⟩
    rw [hx, ← hz, zpow_add, zpow_one, Units.val_mul, hu, map_mul]
    ring
  · rintro ⟨z, hz⟩
    have : coordU κ hκ i x = ϖ * z := by
      apply coordU_eq κ hκ i x
      rw [hz, zpow_add, zpow_one, Units.val_mul, hu, map_mul]
      ring
    rw [this, map_mul]
    have hϖ : ϖ ∈ RingHom.ker θ := by rw [hker]; exact Ideal.mem_span_singleton_self ϖ
    rw [RingHom.mem_ker.mp hϖ, zero_mul]

/-- `τ(u^i) = w_i u^i` from `τ(u) = w_1 u` for a multiplicative `w`. -/
theorem zpow_equivariant (τ : B →+* B) (w : ℤ → K) (hw0 : w 0 = 1)
    (hwadd : ∀ a b, w (a + b) = w a * w b) (h1 : τ (u : B) = algebraMap K B (w 1) * u) (i : ℤ) :
    τ ↑(u ^ i) = algebraMap K B (w i) * ↑(u ^ i) := by
  have hneg : τ ↑(u⁻¹) = algebraMap K B (w (-1)) * ↑(u⁻¹) := by
    have h := congrArg τ (Units.mul_inv u)
    rw [map_mul, map_one, h1] at h
    have hw : w 1 * w (-1) = 1 := by rw [← hwadd, add_neg_cancel, hw0]
    calc τ ↑(u⁻¹) = algebraMap K B (w 1 * w (-1)) * ((u : B) * ↑(u⁻¹)) * τ ↑(u⁻¹) := by
          rw [hw, map_one, Units.mul_inv, one_mul, one_mul]
      _ = algebraMap K B (w (-1)) * ↑(u⁻¹) * (algebraMap K B (w 1) * ↑u * τ ↑(u⁻¹)) := by
          rw [map_mul]; ring
      _ = _ := by rw [h, mul_one]
  induction i using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one, map_one, hw0, map_one, one_mul]
  | succ k ih =>
    rw [zpow_add, zpow_one, Units.val_mul, map_mul, ih, h1, hwadd, map_mul]; ring
  | pred k ih =>
    rw [sub_eq_add_neg, zpow_add, zpow_neg_one, Units.val_mul, map_mul, ih, hneg, hwadd,
      map_mul]; ring

theorem filU_equivariant (τ : B →ₗ[K] B) (hτmul : ∀ x y, τ (x * y) = τ x * τ y)
    (τR : R → R) (hτR : ∀ y, τ (algebraMap R B y) = algebraMap R B (τR y))
    (w : ℤ → K) (hτu : ∀ i, τ ↑(u ^ i) = algebraMap K B (w i) * ↑(u ^ i))
    (i : ℤ) (x : B) (hx : x ∈ filU κ hκ u i) :
    τ x = ↑(u ^ i) * algebraMap R B (κ (w i) * τR (Classical.choose hx)) := by
  conv_lhs => rw [Classical.choose_spec hx]
  rw [hτmul, hτu, hτR, map_mul, hκ]
  ring

theorem mem_filU_map (τ : B →ₗ[K] B) (hτmul : ∀ x y, τ (x * y) = τ x * τ y)
    (τR : R → R) (hτR : ∀ y, τ (algebraMap R B y) = algebraMap R B (τR y))
    (w : ℤ → K) (hτu : ∀ i, τ ↑(u ^ i) = algebraMap K B (w i) * ↑(u ^ i))
    (i : ℤ) (x : B) (hx : x ∈ filU κ hκ u i) : τ x ∈ filU κ hκ u i :=
  ⟨_, filU_equivariant κ hκ τ hτmul τR hτR w hτu i x hx⟩

theorem gU_map (hθK : ∀ c, θ (κ c) = algebraMap K C c)
    (τ : B →ₗ[K] B) (hτmul : ∀ x y, τ (x * y) = τ x * τ y)
    (τR : R → R) (hτR : ∀ y, τ (algebraMap R B y) = algebraMap R B (τR y))
    (τC : C → C) (hθτ : ∀ y, θ (τR y) = τC (θ y))
    (w : ℤ → K) (hτu : ∀ i, τ ↑(u ^ i) = algebraMap K B (w i) * ↑(u ^ i))
    (i : ℤ) (x : filU κ hκ u i) (hx : τ x ∈ filU κ hκ u i) :
    gU κ hκ θ hθK i ⟨τ x, hx⟩ = w i • τC (gU κ hκ θ hθK i x) := by
  rw [gU_apply κ hκ θ hθK i ⟨τ x, hx⟩ (filU_equivariant κ hκ τ hτmul τR hτR w hτu i x x.2),
    gU_apply κ hκ θ hθK i x (Classical.choose_spec x.2), map_mul, hθK, hθτ, Algebra.smul_def]

end DVRFil

end

end DeRhamHTMult
