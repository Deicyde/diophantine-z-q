import ZInQKernel.Model.Field.Valuation

/-!
# Unique factorization in `K₀ˣ`

Blueprint: `model/field/integers-pid.md` (the factorization statement).

`ℤ[s]` is a principal ideal domain (`Zs.isPrincipalIdealRing`), hence a unique factorization
domain with fraction field `K₀`. Fix a set `P` of representatives of the prime elements up to
units. Every `x ∈ K₀ˣ` is `x = u ∏_{π ∈ P} π^{v_π(x)}` with `u ∈ ℤ[s]ˣ` and almost all
`v_π(x) = 0`, and the exponents in any such factorization are the valuations `v_π(x)`.
The valuation rules `v_π(xy) = v_π(x) + v_π(y)` and `v_π(x + y) ≥ min (v_π x) (v_π y)` (equality
when the valuations differ) are `vp_mul`, `min_le_vp_add`, `vp_add_eq_min_of_ne`.
-/

namespace ZInQ

/-- `P` is a set of representatives of the prime elements of `ℤ[s]` up to units. -/
structure IsPrimeReps (P : Set Zs) : Prop where
  prime : ∀ π ∈ P, Prime π
  exists_associated : ∀ q : Zs, Prime q → ∃ π ∈ P, Associated q π
  eq_of_associated : ∀ π ∈ P, ∀ π' ∈ P, Associated π π' → π = π'

/-- A set of representatives exists. -/
theorem exists_isPrimeReps : ∃ P : Set Zs, IsPrimeReps P := by
  -- choose one element in each class of associated elements
  let f : Associates Zs → Zs := Quot.out
  have hf : ∀ q : Zs, Associated (f (Associates.mk q)) q := fun q =>
    Associates.mk_eq_mk_iff_associated.mp (Quot.out_eq (Associates.mk q))
  refine ⟨{π | Prime π ∧ f (Associates.mk π) = π}, ⟨?_, ?_, ?_⟩⟩
  · rintro π ⟨hπ, _⟩; exact hπ
  · intro q hq
    refine ⟨f (Associates.mk q), ⟨(hf q).symm.prime hq, ?_⟩, (hf q).symm⟩
    rw [Associates.mk_eq_mk_iff_associated.mpr (hf q)]
  · rintro π ⟨_, hπ⟩ π' ⟨_, hπ'⟩ h
    rw [← hπ, ← hπ', Associates.mk_eq_mk_iff_associated.mpr h]

variable {P : Set Zs} (hP : IsPrimeReps P)
include hP

theorem IsPrimeReps.vp_rep {π π' : Zs} (hπ : π ∈ P) (hπ' : π' ∈ P) :
    vp π (Zs.toK0 π') = if π = π' then 1 else 0 := by
  have hp := hP.prime π hπ
  have hp' := hP.prime π' hπ'
  split_ifs with h
  · subst h; exact vp_self hp
  · rw [vp_eq_zero_iff hp hp'.ne_zero]
    intro hd
    exact h (hP.eq_of_associated π hπ π' hπ' (hp.associated_of_dvd hp' hd))

/-- The valuation of a product of powers of representatives. -/
theorem IsPrimeReps.vp_prod {S : Finset Zs} (hS : ↑S ⊆ P) (e : Zs → ℤ) {q : Zs} (hq : q ∈ P) :
    vp q (∏ π ∈ S, Zs.toK0 π ^ e π) = if q ∈ S then e q else 0 := by
  classical
  have hqp := hP.prime q hq
  induction S using Finset.induction_on with
  | empty => simp [vp_one hqp]
  | insert a S ha ih =>
    have haP : a ∈ P := hS (Finset.mem_insert_self a S)
    have hSP : ↑S ⊆ P := fun x hx => hS (Finset.mem_insert_of_mem hx)
    have hane : Zs.toK0 a ≠ 0 :=
      (map_ne_zero_iff _ Zs.toK0_injective).mpr (hP.prime a haP).ne_zero
    have hprod : ∏ π ∈ S, Zs.toK0 π ^ e π ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro π hπ
      exact zpow_ne_zero _ ((map_ne_zero_iff _ Zs.toK0_injective).mpr
        (hP.prime π (hSP hπ)).ne_zero)
    rw [Finset.prod_insert ha, vp_mul hqp (zpow_ne_zero _ hane) hprod, vp_zpow hqp,
      hP.vp_rep hq haP, ih hSP]
    by_cases hqa : q = a
    · subst hqa; simp [ha]
    · simp [hqa, Finset.mem_insert]

/-- Factorization of nonzero elements of `ℤ[s]`. -/
theorem IsPrimeReps.exists_factorization_Zs {a : Zs} (ha : a ≠ 0) :
    ∃ S : Finset Zs, ↑S ⊆ P ∧ (∀ π ∈ P, vp π (Zs.toK0 a) ≠ 0 → π ∈ S) ∧
      ∃ u : Zsˣ, Zs.toK0 a = Zs.toK0 u * ∏ π ∈ S, Zs.toK0 π ^ vp π (Zs.toK0 a) := by
  classical
  induction a using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl ha
  | h₂ x hx =>
    refine ⟨∅, by simp, fun π hπ hv => absurd (vp_isUnit (hP.prime π hπ) hx) hv, hx.unit, ?_⟩
    simp
  | h₃ a p ha0 hp ih =>
    obtain ⟨S, hSP, hSsupp, u, hu⟩ := ih ha0
    obtain ⟨π₀, hπ₀P, w, hw⟩ := hP.exists_associated p hp
    -- `p w = π₀`
    have hpa : p * a ≠ 0 := mul_ne_zero hp.ne_zero ha0
    have hpK : Zs.toK0 p ≠ 0 := (map_ne_zero_iff _ Zs.toK0_injective).mpr hp.ne_zero
    have haK : Zs.toK0 a ≠ 0 := (map_ne_zero_iff _ Zs.toK0_injective).mpr ha0
    have hvp : ∀ π ∈ P, vp π (Zs.toK0 p) = if π = π₀ then 1 else 0 := by
      intro π hπ
      have : Zs.toK0 p = Zs.toK0 π₀ * Zs.toK0 ((w⁻¹ : Zsˣ) : Zs) := by
        rw [← hw, ← map_mul, mul_assoc, Units.mul_inv, mul_one]
      have hπp := hP.prime π hπ
      rw [this, vp_mul hπp ((map_ne_zero_iff _ Zs.toK0_injective).mpr
        (hP.prime π₀ hπ₀P).ne_zero) ((map_ne_zero_iff _ Zs.toK0_injective).mpr (w⁻¹).ne_zero),
        vp_unit hπp, add_zero, hP.vp_rep hπ hπ₀P]
    refine ⟨insert π₀ S, ?_, ?_, u * w⁻¹, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hπ₀P
      · exact hSP hx
    · intro π hπ hv
      rw [map_mul, vp_mul (hP.prime π hπ) hpK haK, hvp π hπ] at hv
      by_cases h : π = π₀
      · rw [h]; exact Finset.mem_insert_self _ _
      · rw [ite_eq_right_iff.mpr (fun h' => absurd h' h), zero_add] at hv
        exact Finset.mem_insert_of_mem (hSsupp π hπ hv)
    · have hexp : ∀ π ∈ insert π₀ S, vp π (Zs.toK0 (p * a)) =
          (if π = π₀ then 1 else 0) + vp π (Zs.toK0 a) := by
        intro π hπ
        have hπP : π ∈ P := by
          rcases Finset.mem_insert.mp hπ with rfl | hx
          · exact hπ₀P
          · exact hSP hx
        rw [map_mul, vp_mul (hP.prime π hπP) hpK haK, hvp π hπP]
      have hne : ∀ π ∈ insert π₀ S, Zs.toK0 π ≠ 0 := by
        intro π hπ
        have hπP : π ∈ P := by
          rcases Finset.mem_insert.mp hπ with rfl | hx
          · exact hπ₀P
          · exact hSP hx
        exact (map_ne_zero_iff _ Zs.toK0_injective).mpr (hP.prime π hπP).ne_zero
      rw [Finset.prod_congr rfl (fun π hπ => by rw [hexp π hπ, zpow_add₀ (hne π hπ)]),
        Finset.prod_mul_distrib]
      -- the first product is `π₀`
      have h1 : ∏ π ∈ insert π₀ S, Zs.toK0 π ^ (if π = π₀ then (1 : ℤ) else 0) = Zs.toK0 π₀ := by
        rw [Finset.prod_eq_single π₀]
        · simp
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_insert_self _ _) h
      -- the second product is the one over `S`
      have h2 : ∏ π ∈ insert π₀ S, Zs.toK0 π ^ vp π (Zs.toK0 a) =
          ∏ π ∈ S, Zs.toK0 π ^ vp π (Zs.toK0 a) := by
        by_cases hmem : π₀ ∈ S
        · rw [Finset.insert_eq_of_mem hmem]
        · rw [Finset.prod_insert hmem]
          have : vp π₀ (Zs.toK0 a) = 0 := by
            by_contra hv; exact hmem (hSsupp π₀ hπ₀P hv)
          rw [this, zpow_zero, one_mul]
      set prodA := ∏ π ∈ S, Zs.toK0 π ^ vp π (Zs.toK0 a) with hprodA
      rw [h1, h2, map_mul, hu, ← hw]
      simp only [map_mul, Units.val_mul]
      have hwK : Zs.toK0 (w : Zs) * Zs.toK0 ((w⁻¹ : Zsˣ) : Zs) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      linear_combination (-(Zs.toK0 p * Zs.toK0 (u : Zs) * prodA)) * hwK

/-- **Unique factorization in `K₀ˣ`.** For `x ∈ K₀ˣ` there is a finite set `S ⊆ P` containing
every `π ∈ P` with `v_π(x) ≠ 0` and a unit `u` with `x = u ∏_{π ∈ S} π^{v_π(x)}`. -/
theorem IsPrimeReps.exists_factorization {x : K0} (hx : x ≠ 0) :
    ∃ S : Finset Zs, ↑S ⊆ P ∧ (∀ π ∈ P, vp π x ≠ 0 → π ∈ S) ∧
      ∃ u : Zsˣ, x = Zs.toK0 u * ∏ π ∈ S, Zs.toK0 π ^ vp π x := by
  classical
  obtain ⟨a, b, hb, rfl⟩ := exists_eq_div_Zs x
  have ha : a ≠ 0 := by rintro rfl; simp at hx
  have haK : Zs.toK0 a ≠ 0 := (map_ne_zero_iff _ Zs.toK0_injective).mpr ha
  have hbK : Zs.toK0 b ≠ 0 := (map_ne_zero_iff _ Zs.toK0_injective).mpr hb
  obtain ⟨Sa, hSaP, hSa, ua, hua⟩ := hP.exists_factorization_Zs ha
  obtain ⟨Sb, hSbP, hSb, ub, hub⟩ := hP.exists_factorization_Zs hb
  have hSP : ↑(Sa ∪ Sb) ⊆ P := by
    intro π hπ; rcases Finset.mem_union.mp hπ with h | h
    · exact hSaP h
    · exact hSbP h
  -- extend both products to `Sa ∪ Sb`
  have hext : ∀ (c : Zs) (Sc : Finset Zs), Sc ⊆ Sa ∪ Sb → (∀ π ∈ P, vp π (Zs.toK0 c) ≠ 0 → π ∈ Sc) →
      ∏ π ∈ Sc, Zs.toK0 π ^ vp π (Zs.toK0 c) = ∏ π ∈ Sa ∪ Sb, Zs.toK0 π ^ vp π (Zs.toK0 c) := by
    intro c Sc hsub hsupp
    apply Finset.prod_subset hsub
    intro π hπ hπc
    have : vp π (Zs.toK0 c) = 0 := by
      by_contra hv; exact hπc (hsupp π (hSP hπ) hv)
    rw [this, zpow_zero]
  refine ⟨Sa ∪ Sb, hSP, ?_, ua * ub⁻¹, ?_⟩
  · intro π hπ hv
    rw [vp_div (hP.prime π hπ) haK hbK] at hv
    by_cases h1 : vp π (Zs.toK0 a) = 0
    · exact Finset.mem_union_right _ (hSb π hπ (by omega))
    · exact Finset.mem_union_left _ (hSa π hπ h1)
  · have hne : ∀ π ∈ Sa ∪ Sb, Zs.toK0 π ≠ 0 := fun π hπ =>
      (map_ne_zero_iff _ Zs.toK0_injective).mpr (hP.prime π (hSP hπ)).ne_zero
    rw [Finset.prod_congr rfl (fun π hπ => by
      rw [vp_div (hP.prime π (hSP hπ)) haK hbK, zpow_sub₀ (hne π hπ)]),
      Finset.prod_div_distrib, ← hext a Sa Finset.subset_union_left hSa,
      ← hext b Sb Finset.subset_union_right hSb]
    set prodA := ∏ π ∈ Sa, Zs.toK0 π ^ vp π (Zs.toK0 a) with hprodA
    set prodB := ∏ π ∈ Sb, Zs.toK0 π ^ vp π (Zs.toK0 b) with hprodB
    rw [hua, hub]
    have hubK : Zs.toK0 (ub : Zs) ≠ 0 := (map_ne_zero_iff _ Zs.toK0_injective).mpr ub.ne_zero
    have hprodb : prodB ≠ 0 := by
      rw [hprodB, Finset.prod_ne_zero_iff]; intro π hπ
      exact zpow_ne_zero _ (hne π (Finset.mem_union_right _ hπ))
    have hinv : Zs.toK0 ((ub⁻¹ : Zsˣ) : Zs) = (Zs.toK0 (ub : Zs))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    simp only [Units.val_mul, map_mul, hinv]
    field_simp

/-- **Uniqueness of the exponents.** If `x = u ∏_{π ∈ S} π^{e(π)}` with `S ⊆ P` finite, then
`e(π) = v_π(x)` for `π ∈ S` and `v_π(x) = 0` for `π ∈ P \ S`. -/
theorem IsPrimeReps.vp_eq_of_factorization {S : Finset Zs} (hS : ↑S ⊆ P) (e : Zs → ℤ) (u : Zsˣ)
    {x : K0} (hx : x = Zs.toK0 u * ∏ π ∈ S, Zs.toK0 π ^ e π) {q : Zs} (hq : q ∈ P) :
    vp q x = if q ∈ S then e q else 0 := by
  have hqp := hP.prime q hq
  have hprod : ∏ π ∈ S, Zs.toK0 π ^ e π ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]; intro π hπ
    exact zpow_ne_zero _ ((map_ne_zero_iff _ Zs.toK0_injective).mpr (hP.prime π (hS hπ)).ne_zero)
  rw [hx, vp_mul hqp ((map_ne_zero_iff _ Zs.toK0_injective).mpr u.ne_zero) hprod, vp_unit hqp,
    zero_add, hP.vp_prod hS e hq]

end ZInQ
