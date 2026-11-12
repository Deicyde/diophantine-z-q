
/-! ## glue-b3b: `LeafB3b` is glue

`ℚ(√p*)` is ramified at `p`, proved without discriminants: with `α` the quadratic Gauss sum
(`α² = ±p`), `H` the stabilizer of `α` and `A = B^H` (the algebraic integers fixed by `H`),
Mathlib's profinite transitivity over `A` and its surjectivity of the stabilizer of a prime onto
the automorphisms of the residue extension (`Ideal.Quotient.stabilizerHom_surjective_of_profinite`)
produce an element of the inertia group of `w` with `s α = -α`. The input "the residue extension
of `A` is trivial" is replaced by valuation arithmetic: `v(α)² = v(p)`. -/

section B3b

open scoped Pointwise

variable {w : ValuationSubring Qbar} {p : ℕ}

theorem val_natCast_ne_zero (hp : p.Prime) : w.valuation (p : Qbar) ≠ 0 := by
  rw [Ne, Valuation.zero_iff]; exact_mod_cast hp.ne_zero

theorem isIntegral_intCast (r : ℤ) : IsIntegral ℤ (r : Qbar) := by
  simpa using isIntegral_algebraMap (R := ℤ) (A := Qbar) (x := r)

theorem val_intCast_le_one (r : ℤ) : w.valuation (r : Qbar) ≤ 1 :=
  val_le_one_of_isIntegral w (isIntegral_intCast r)

/-- At a place over `p`, an integer has valuation `1` or at most `v(p)`. -/
theorem val_intCast (hp : p.Prime) (hw : LiesOver w p) (r : ℤ) :
    w.valuation (r : Qbar) = 1 ∨ w.valuation (r : Qbar) ≤ w.valuation (p : Qbar) := by
  by_cases hd : (p : ℤ) ∣ r
  · obtain ⟨k, rfl⟩ := hd
    right
    rw [Int.cast_mul, map_mul, Int.cast_natCast]
    exact mul_le_of_le_one_right' (val_intCast_le_one k)
  · left
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hcop : IsCoprime (p : ℤ) r := (Irreducible.coprime_iff_not_dvd hpr.irreducible).mpr hd
    obtain ⟨x, y, hxy⟩ := hcop
    have h1 := congrArg (fun z : ℤ => w.valuation (z : Qbar)) hxy
    simp only [Int.cast_add, Int.cast_mul, Int.cast_one, map_one, Int.cast_natCast] at h1
    refine le_antisymm (val_intCast_le_one r) ?_
    by_contra hlt
    push_neg at hlt
    have h2 : w.valuation ((x : Qbar) * p + y * r) < 1 := by
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one x)) hw
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_intCast_le_one y)) hlt
    rw [h1] at h2; exact lt_irrefl _ h2

theorem val_sq_eq {α : Qbar} {c : ℤ} (hα : α ^ 2 = (c : Qbar))
    (hc : w.valuation (c : Qbar) = w.valuation (p : Qbar)) :
    w.valuation α * w.valuation α = w.valuation (p : Qbar) := by
  rw [← map_mul, ← pow_two, hα, hc]

/-- **The valuation input.** If `α² = c ∈ ℤ` with `v(c) = v(p)` (e.g. `c = ±p`), `a, b` are `w`-integral and `(a - b) α ∈ ℤ`, then
`a ≡ b` modulo `w`: since `v(α)` lies strictly between `v(p)` and `1`, while an integer has
valuation `1` or `≤ v(p)`. -/
theorem val_sub_lt_one (hp : p.Prime) (hw : LiesOver w p) {α : Qbar} {c : ℤ}
    (hα : α ^ 2 = (c : Qbar)) (hc : w.valuation (c : Qbar) = w.valuation (p : Qbar)) {a b : Qbar}
    (ha : w.valuation a ≤ 1) (hb : w.valuation b ≤ 1) (r : ℤ) (hr : (a - b) * α = r) :
    w.valuation (a - b) < 1 := by
  have hu := val_sq_eq (w := w) hα hc
  have hab : w.valuation (a - b) ≤ 1 := le_trans (Valuation.map_sub _ _ _) (max_le ha hb)
  have hu0 : w.valuation α ≠ 0 := by
    intro h; rw [h, zero_mul] at hu; exact val_natCast_ne_zero hp hu.symm
  have hu1 : w.valuation α < 1 := by
    by_contra h; push_neg at h
    have : (1 : _) ≤ w.valuation α * w.valuation α := one_le_mul h h
    rw [hu] at this; exact absurd hw (not_lt.mpr this)
  have hvr : w.valuation (r : Qbar) = w.valuation (a - b) * w.valuation α := by
    rw [← hr, map_mul]
  rcases val_intCast hp hw r with h1 | h1
  · rw [h1] at hvr
    have : w.valuation (a - b) * w.valuation α < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_left' hab) hu1
    rw [← hvr] at this; exact absurd this (lt_irrefl _)
  · rw [hvr, ← hu] at h1
    have h2 := mul_le_mul_left h1 (w.valuation α)⁻¹
    rw [mul_inv_cancel_right₀ hu0, mul_inv_cancel_right₀ hu0] at h2
    exact lt_of_le_of_lt h2 hu1

theorem smul_sq_cases {α : Qbar} {c : ℤ} (hα : α ^ 2 = (c : Qbar)) (g : Gal) :
    g α = α ∨ g α = -α := by
  have hc : g (α ^ 2) = α ^ 2 := by rw [hα, map_intCast]
  rw [map_pow] at hc
  exact sq_eq_sq_iff_eq_or_eq_neg.mp hc

theorem exists_int_of_fixed {y : Qbar} (hy : IsIntegral ℤ y) (hfix : ∀ g : Gal, g y = y) :
    ∃ r : ℤ, y = r := by
  have hbot : y ∈ (⊥ : IntermediateField ℚ Qbar) := (InfiniteGalois.mem_bot_iff_fixed y).mpr hfix
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hbot
  have hint : IsIntegral ℤ (algebraMap ℚ Qbar q) := by rw [hq]; exact hy
  rw [isIntegral_algebraMap_iff] at hint
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  exact ⟨n, by rw [← hq]; simp⟩

/-- **Anti-invariance.** If `a` is fixed by every `g` fixing `α` and `σ α = -α`, then
`(a - σ a) α` is fixed by all of `G_ℚ`, hence an integer when `a` is integral. -/
theorem exists_int_anti {α a : Qbar} {c : ℤ} (hα : α ^ 2 = (c : Qbar))
    (hαi : IsIntegral ℤ α) (hai : IsIntegral ℤ a) (hfix : ∀ g : Gal, g α = α → g a = a)
    (σ : Gal) (hσ : σ α = -α) : ∃ r : ℤ, (a - σ a) * α = r := by
  have hσi : σ⁻¹ α = -α := by
    have h2 : (σ⁻¹ : Gal) (σ α) = α := by
      show (σ⁻¹ * σ) α = α
      rw [inv_mul_cancel]; rfl
    rw [hσ, map_neg] at h2
    exact neg_eq_iff_eq_neg.mp h2
  refine exists_int_of_fixed ?_ ?_
  · exact ((hai.sub (hai.map ((σ : Qbar →+* Qbar).toIntAlgHom))).mul hαi)
  intro g
  rw [map_mul, map_sub]
  rcases smul_sq_cases hα g with hg | hg
  · have h1 : g a = a := hfix g hg
    have h2 : (σ⁻¹ * g * σ) a = a := hfix _ (by
      show (σ⁻¹ : Gal) (g (σ α)) = α
      rw [hσ, map_neg, hg, map_neg, hσi, neg_neg])
    have h3 : g (σ a) = σ a := by
      have e : g (σ a) = σ ((σ⁻¹ * g * σ) a) := by
        show g (σ a) = (σ * (σ⁻¹ * g * σ)) a
        rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]; rfl
      rw [e, h2]
    rw [h1, h3, hg]
  · have h1 : (σ⁻¹ * g) a = a := hfix _ (by
      show (σ⁻¹ : Gal) (g α) = α
      rw [hg, map_neg, hσi, neg_neg])
    have h1' : g a = σ a := by
      have e : g a = σ ((σ⁻¹ * g) a) := by
        show g a = (σ * (σ⁻¹ * g)) a
        rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [e, h1]
    have h2 : (g * σ) a = a := hfix _ (by
      show g (σ α) = α
      rw [hσ, map_neg, hg, neg_neg])
    have h2' : g (σ a) = a := h2
    rw [h1', h2', hg]; ring

/-- Elements of `w` are fractions `n / d` of algebraic integers with `v(d) = 1`. -/
theorem exists_frac (hp : p.Prime) (hw : LiesOver w p) (x : Qbar) (hx : x ∈ w) :
    ∃ n d : Qbar, IsIntegral ℤ n ∧ IsIntegral ℤ d ∧ w.valuation d = 1 ∧ x * d = n := by
  let K : IntermediateField ℚ Qbar := IntermediateField.adjoin ℚ {x}
  have : FiniteDimensional ℚ K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ) x)
  have : NumberField K := ⟨⟩
  let ι : 𝓞 K →+* Qbar := (algebraMap K Qbar).comp (algebraMap (𝓞 K) K)
  have hint : ∀ r : 𝓞 K, IsIntegral ℤ (ι r) := fun r =>
    (RingOfIntegers.isIntegral_coe r).map (IsScalarTower.toAlgHom ℤ K Qbar)
  let f : 𝓞 K →+* w :=
    { toFun := fun r => ⟨ι r, mem_of_isIntegral w (hint r)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  let I : Ideal (𝓞 K) := (IsLocalRing.maximalIdeal w).comap f
  have hI : ∀ r, r ∈ I ↔ w.valuation (ι r) < 1 := fun r =>
    (w.valuation_lt_one_iff (f r))
  have hpI : (p : 𝓞 K) ∈ I := by rw [hI]; simpa [ι, LiesOver] using hw
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨I, Ideal.comap_isPrime _ _, fun h => hp0 (by rw [h] at hpI; simpa using hpI)⟩
  let x' : K := ⟨x, IntermediateField.mem_adjoin_simple_self ℚ x⟩
  obtain ⟨n, d, h⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := K) x'
  have hd : ¬ w.valuation (ι d) < 1 := fun h' => d.2 ((hI d).mpr h')
  have hd1 : w.valuation (ι d) = 1 :=
    le_antisymm (val_le_one_of_isIntegral w (hint d)) (not_lt.mp hd)
  rcases h with h | h
  · have h' : x * ι d = ι n := by
      have := congrArg (algebraMap K Qbar) h
      simpa [ι] using this
    exact ⟨ι n, ι d, hint n, hint d, hd1, h'⟩
  · have h' : x * ι n = ι d := by
      have := congrArg (algebraMap K Qbar) h
      simpa [ι] using this
    have hx1 : w.valuation x ≤ 1 := (w.valuation_le_one_iff x).mpr hx
    have hn1 : w.valuation (ι n) ≤ 1 := val_le_one_of_isIntegral w (hint n)
    have hn : w.valuation (ι n) = 1 := by
      refine le_antisymm hn1 ?_
      have e := congrArg w.valuation h'
      rw [map_mul, hd1] at e
      rw [← e]; exact mul_le_of_le_one_left' hx1
    exact ⟨ι d, ι n, hint d, hint n, hn, h'⟩

/-- An element stabilizing the center `𝔓_w` and acting trivially on `B/𝔓_w` lies in the
inertia group `I_w`. -/
theorem mem_inertia_of_center (hp : p.Prime) (hw : LiesOver w p) (s : Gal)
    (hsQ : s • centerIdeal w = centerIdeal w)
    (hsb : ∀ b : B, s • b - b ∈ centerIdeal w) :
    s ∈ (w.inertiaSubgroup ℚ).map (w.decompositionSubgroup ℚ).subtype := by
  have hcs : centerIdeal (s • w) = centerIdeal w := by rw [centerIdeal_smul, hsQ]
  have hc : ∀ y : Qbar, IsIntegral ℤ y → ((s • w).valuation y < 1 ↔ w.valuation y < 1) := by
    intro y hy
    have h := congrArg (fun I : Ideal B => (⟨y, (mem_integralClosure_iff ℤ Qbar).mpr hy⟩ : B) ∈ I)
      hcs
    simp only [mem_centerIdeal] at h
    exact h.to_iff
  have hpint : IsIntegral ℤ (p : Qbar) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := Qbar) (x := (p : ℤ))
  have hw' : (s • w).valuation (p : Qbar) < 1 := (hc _ hpint).mpr hw
  have heq : s • w = w :=
    le_antisymm (le_of_center (s • w) w p hp hw' hc)
      (le_of_center w (s • w) p hp hw (fun y hy => (hc y hy).symm))
  have hdec : s ∈ w.decompositionSubgroup ℚ := heq
  refine Subgroup.mem_map.mpr ⟨⟨s, hdec⟩, ?_, rfl⟩
  have hB : ∀ y : Qbar, IsIntegral ℤ y → w.valuation (s y - y) < 1 := by
    intro y hy
    have := hsb ⟨y, (mem_integralClosure_iff ℤ Qbar).mpr hy⟩
    rw [mem_centerIdeal] at this
    exact this
  change _ = (1 : _)
  ext r
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨s, hdec⟩ : w.decompositionSubgroup ℚ) • IsLocalRing.residue w y =
    IsLocalRing.residue w y
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  show w.valuation (s (y : Qbar) - y) < 1
  obtain ⟨n, d, hn, hd, hd1, hnd⟩ := exists_frac hp hw (y : Qbar) y.2
  have hsd : w.valuation (s d) = 1 := by
    refine le_antisymm (val_le_one_of_isIntegral w (hd.map ((s : Qbar →+* Qbar).toIntAlgHom)))
      (not_lt.mp fun h => ?_)
    have h1 : (⟨s d, (mem_integralClosure_iff ℤ Qbar).mpr
        (hd.map ((s : Qbar →+* Qbar).toIntAlgHom))⟩ : B) ∈ s • centerIdeal w := by
      rw [hsQ, mem_centerIdeal]; exact h
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_centerIdeal] at h1
    have h2 : ((s⁻¹ • (⟨s d, (mem_integralClosure_iff ℤ Qbar).mpr
        (hd.map ((s : Qbar →+* Qbar).toIntAlgHom))⟩ : B) : B) : Qbar) = d := by
      show (s⁻¹ : Gal) (s d) = d
      show (s⁻¹ * s) d = d
      rw [inv_mul_cancel]; rfl
    rw [h2, hd1] at h1; exact lt_irrefl _ h1
  have hsnd : s (y : Qbar) * s d = s n := by rw [← map_mul, hnd]
  have key : (s (y : Qbar) - y) * (d * s d) = (s n - n) * d - n * (s d - d) := by
    linear_combination d * hsnd - s d * hnd
  have hv := congrArg w.valuation key
  rw [map_mul, map_mul, hd1, hsd, one_mul, mul_one] at hv
  rw [hv]
  refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
  · rw [map_mul, hd1, mul_one]; exact hB n hn
  · rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_le_one_of_isIntegral w hn)) (hB d hd)

end B3b
