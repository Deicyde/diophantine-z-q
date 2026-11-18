import DecompositionFromCenterV003
import ValuationLocalizationV001

/-!
# Inertia is determined by the action on integral elements modulo the center

Let `O` be a discrete valuation subring of a field `K` of characteristic zero, `Ω/K` algebraic, and
`w` a valuation subring of `Ω` with `w ∩ K = O`. If a `K`-automorphism `σ` of `Ω` moves every element
integral over `O` by an element of the maximal ideal of `w` (`v(σ s − s) < 1`), then `σ` lies in the
inertia subgroup of `w`.

Every element of `w` is a quotient `a / s` of integral elements with `s` a unit of `w`
(`exists_integral_fraction`: the valuation ring of `K(x)` is the localization of the integral
closure at its center). Hence `σ` preserves `w` and acts trivially on its residue field.
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

open scoped Pointwise

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- **Elements of `w` are fractions of integral elements with unit denominators.** -/
theorem exists_integral_fraction [CharZero K] [Algebra.IsAlgebraic K Ω] (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    {x : Ω} (hx : x ∈ w) :
    ∃ a s : Ω, IntegralOver O a ∧ IntegralOver O s ∧ w.valuation s = 1 ∧ x = a * s⁻¹ := by
  classical
  let N : IntermediateField K Ω := IntermediateField.adjoin K {x}
  have : FiniteDimensional K N :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  let _ : Algebra O Ω := ((algebraMap K Ω).comp (algebraMap O K)).toAlgebra
  have : IsScalarTower O K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let B := integralClosure O N
  have : IsDedekindDomain B := integralClosure.isDedekindDomain O K N
  have : IsFractionRing B N := integralClosure.isFractionRing_of_finite_extension (A := O) K N
  let f₁ : N →+* Ω := N.val.toRingHom
  let W := w.comap f₁
  have hint : ∀ b : B, IntegralOver O ((b : N) : Ω) := by
    intro b
    have hb : IsIntegral O (b : N) := b.2
    exact hb.map (N.val.restrictScalars O)
  have h₁ : ∀ b : B, algebraMap B N b ∈ W := fun b =>
    ValuationSubring.mem_comap.mpr (mem_of_integralOver O w hw (hint b))
  have hxN : x ∈ N := IntermediateField.mem_adjoin_simple_self K x
  have hxW : (⟨x, hxN⟩ : N) ∈ W := ValuationSubring.mem_comap.mpr hx
  obtain ⟨a, s, hs, e⟩ := exists_eq_div_of_mem W h₁ hxW
  refine ⟨((a : N) : Ω), ((s : N) : Ω), hint a, hint s, ?_, ?_⟩
  · have hle : w.valuation ((s : N) : Ω) ≤ 1 :=
      (w.valuation_le_one_iff _).2 (mem_of_integralOver O w hw (hint s))
    have hnot : ¬ w.valuation ((s : N) : Ω) < 1 := by
      intro hlt
      apply hs
      rw [mem_center_iff, comap_valuation_lt_one_iff]
      exact hlt
    exact le_antisymm hle (not_lt.mp hnot)
  · have := congrArg (fun z : N => (z : Ω)) e
    simpa using this

/-- **Inertia from the action on integral elements.** -/
theorem mem_inertia_of_integral [CharZero K] [Algebra.IsAlgebraic K Ω] (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hres : ∀ s : Ω, IntegralOver O s → w.valuation (σ s - s) < 1) :
    ∃ h : σ ∈ w.decompositionSubgroup K,
      (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K := by
  -- the center is preserved
  have hσ : ∀ s : Ω, IntegralOver O s → (w.valuation s < 1 ↔ w.valuation (σ s) < 1) := by
    intro s hs
    have hd := hres s hs
    constructor
    · intro hlt
      have : σ s = (σ s - s) + s := by ring
      rw [this]
      exact Valuation.map_add_lt _ hd hlt
    · intro hlt
      have : s = σ s - (σ s - s) := by ring
      rw [this]
      exact Valuation.map_sub_lt _ hlt hd
  have hD := mem_decompositionSubgroup_of_center O w hw σ hσ
  refine ⟨hD, ?_⟩
  -- trivial action on the residue field
  have hmove : ∀ u : Ω, u ∈ w → w.valuation (σ u - u) < 1 := by
    intro u hu
    obtain ⟨a, s, ha, hs, hs1, rfl⟩ := exists_integral_fraction O w hw hu
    have has : w.valuation (σ s) = 1 := by
      have h1 := hres s hs
      rw [← hs1] at h1 ⊢
      have := Valuation.map_add_eq_of_lt_right w.valuation (x := σ s - s) (y := s) h1
      simpa using this
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hs1
      exact zero_ne_one hs1
    have hσs0 : σ s ≠ 0 := (map_ne_zero σ).mpr hs0
    have hav : w.valuation a ≤ 1 := (w.valuation_le_one_iff a).2 (mem_of_integralOver O w hw ha)
    have key : σ (a * s⁻¹) - a * s⁻¹ =
        ((σ a - a) * s - a * (σ s - s)) * (σ s * s)⁻¹ := by
      rw [map_mul, map_inv₀]
      field_simp
      ring
    rw [key, Valuation.map_mul, Valuation.map_inv, Valuation.map_mul, has, hs1, one_mul, inv_one,
      mul_one]
    apply Valuation.map_sub_lt
    · rw [Valuation.map_mul, hs1, mul_one]
      exact hres a ha
    · rw [Valuation.map_mul]
      calc w.valuation a * w.valuation (σ s - s) ≤ 1 * w.valuation (σ s - s) :=
            mul_le_mul_of_nonneg_right hav zero_le
        _ = w.valuation (σ s - s) := one_mul _
        _ < 1 := hres s hs
  rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
  apply RingEquiv.ext
  intro r
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective r
  change (⟨σ, hD⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w u = IsLocalRing.residue w u
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact hmove u u.2

end InertiaPointDescent
