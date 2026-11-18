import InertiaFieldUnramifiedV003
import UnramifiedValuationV002
import InertiaRestrictConcreteV002
import ResidueFieldFiniteV002
import Mathlib.FieldTheory.Normal.Closure

/-!
# Fields fixed by inertia are unramified at `w`

Let `K` be a number field, `O ⊆ K` a discrete valuation subring with uniformizer `ϖ`, `Ω` an
algebraic closure of `K`, and `w` a valuation subring of `Ω` with `w ∩ K = O`. If a finite
intermediate field `M` is fixed pointwise by the inertia subgroup of `w`, then `ϖ` generates the
maximal ideal of `w ∩ M`: every `x ∈ M` with `v_w(x) < 1` satisfies `x / ϖ ∈ w`. That is, `w ∩ M` is
unramified over `O` (ramification index one).

Proof: let `N` be the normal closure of `M` in `Ω`, `S` the integral closure of `O` in `N` and `P` the
center of `w` on `S`. Inertia of `w` restricts onto the inertia group of `P` in `Gal(N/K)`, so `M`
lies in the inertia field of `P`; the prime of the integral closure of `O` in `M` below `P` has
ramification index one; and ramification index one at the center gives the valuation statement.
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

open IsLocalRing

/-- Membership in the maximal ideal of `O` in terms of `w`. -/
theorem mem_maximalIdeal_iff_val {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (O : ValuationSubring K) (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (a : O) : a ∈ maximalIdeal O ↔ w.valuation (algebraMap K Ω (a : K)) < 1 := by
  rw [ValuationSubring.valuation_lt_one_iff, ← comap_valuation_lt_one_iff, hw]

variable {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

/-- **Fields fixed by the inertia of `w` are unramified at `w`.** -/
theorem div_uniformizer_mem_of_inertia_fixed (O : ValuationSubring K) [IsDiscreteValuationRing O]
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (M : IntermediateField K Ω) [FiniteDimensional K M]
    (hM : ∀ m ∈ M, ∀ σ : Ω ≃ₐ[K] Ω, (∃ h : σ ∈ w.decompositionSubgroup K,
      (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K) → σ m = m)
    (ϖ : O) (hϖ : Irreducible ϖ) (x : Ω) (hxM : x ∈ M) (hx : w.valuation x < 1) :
    x * (algebraMap K Ω (ϖ : K))⁻¹ ∈ w := by
  classical
  -- the normal closure
  let N : IntermediateField K Ω := IntermediateField.normalClosure K M Ω
  have hMN : M ≤ N := IntermediateField.le_normalClosure M
  have : Normal K Ω := IsAlgClosure.normal K Ω
  have : FiniteDimensional K N := normalClosure.is_finiteDimensional K M Ω
  have : Normal K N := normalClosure.normal K M Ω
  have : IsGalois K N :=
    { to_isSeparable := Algebra.IsAlgebraic.isSeparable_of_perfectField
      to_normal := ‹Normal K N› }
  let _ : Algebra O N := ((algebraMap K N).comp (algebraMap O K)).toAlgebra
  have : IsScalarTower O K N := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let S := integralClosure O N
  have hfrS : IsFractionRing S N := integralClosure.isFractionRing_of_finite_extension (A := O) K N
  have hdS : IsDedekindDomain S := integralClosure.isDedekindDomain O K N
  let WN : ValuationSubring N := w.comap (algebraMap N Ω)
  have hBN : ∀ b : S, algebraMap S N b ∈ WN := fun b =>
    ValuationSubring.mem_comap.mpr
      (mem_of_integralOver O w hw (integralOver_val O N (x := (b : N)) b.2))
  let P : Ideal S := center WN hBN
  have hPmem : ∀ b : S, b ∈ P ↔ w.valuation (((b : N) : Ω)) < 1 := by
    intro b
    rw [mem_center_iff, comap_valuation_lt_one_iff]
    rfl
  have hlies : P.LiesOver (maximalIdeal O) := by
    constructor
    ext a
    rw [Ideal.mem_comap, hPmem, mem_maximalIdeal_iff_val O w hw]
    rfl
  have hfin : Finite (O ⧸ maximalIdeal O) := finite_residueField K O
  -- the field `M` inside `N`
  let F : IntermediateField K N := IntermediateField.restrict hMN
  have hF : F ≤ inertiaField O K N P := by
    intro y hy
    rw [IntermediateField.mem_restrict] at hy
    change ∀ τ : (P.inertia (N ≃ₐ[K] N)), τ • y = y
    intro τ
    have hτ : (τ : N ≃ₐ[K] N) ∈ (centerIdealN O w hw N).inertia (N ≃ₐ[K] N) := by
      intro s
      have h := τ.2 ⟨(s : N), s.2⟩
      rw [Submodule.mem_toAddSubgroup, hPmem] at h
      rw [Submodule.mem_toAddSubgroup, centerIdealN, Ideal.mem_comap, mem_centerIdeal_iff]
      exact h
    have := inertia_fixes_of_fixedField O w hw N (m := (y : Ω)) y.2
      (fun σ hσ => hM (y : Ω) hy σ hσ) (τ : N ≃ₐ[K] N) hτ
    exact this
  have he := ramificationIdx_eq_one_of_le_inertiaField O K N (maximalIdeal O) P F hF
  -- the valuation statement on `F`
  let B := integralClosure O F
  have hfrB : IsFractionRing B F := integralClosure.isFractionRing_of_finite_extension (A := O) K F
  have hdB : IsDedekindDomain B := integralClosure.isDedekindDomain O K F
  let WF : ValuationSubring F := WN.comap (algebraMap F N)
  have hBF : ∀ b : B, algebraMap B F b ∈ WF := fun b =>
    ValuationSubring.mem_comap.mpr (hBN (inclF O K N F b))
  have hcenter : center WF hBF = P.comap (inclF O K N F) := by
    ext b
    rw [mem_center_iff, Ideal.mem_comap, hPmem, comap_valuation_lt_one_iff,
      comap_valuation_lt_one_iff]
    rfl
  have hϖspan : (center WF hBF).under O = Ideal.span {ϖ} := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
    ext a
    rw [Ideal.mem_comap, hcenter, Ideal.mem_comap, hPmem, mem_maximalIdeal_iff_val O w hw]
    rfl
  rw [← hcenter] at he
  let y : F := ⟨⟨x, hMN hxM⟩, (IntermediateField.mem_restrict hMN _).2 hxM⟩
  have hy : WF.valuation y < 1 := by
    rw [comap_valuation_lt_one_iff, comap_valuation_lt_one_iff]
    exact hx
  have hle := val_le_of_ramificationIdx_eq_one WF hBF ϖ hϖspan he y hy
  have hϖ0 : (ϖ : K) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  set z : F := algebraMap B F (algebraMap O B ϖ) with hz
  have hzΩ : (((z : N) : Ω)) = algebraMap K Ω (ϖ : K) := rfl
  have hz0 : z ≠ 0 := by
    intro h0
    have := congrArg (fun u : F => ((u : N) : Ω)) h0
    change (((z : N) : Ω)) = ((((0 : F) : N) : Ω)) at this
    rw [hzΩ] at this
    exact hϖ0 ((map_eq_zero_iff _ (algebraMap K Ω).injective).1 (this.trans (by rfl)))
  have hmem : y * z⁻¹ ∈ WF := by
    rw [← WF.valuation_le_one_iff, Valuation.map_mul, Valuation.map_inv,
      ← div_eq_mul_inv]
    exact div_le_one_of_le₀ hle zero_le
  have hmem' := ValuationSubring.mem_comap.mp (ValuationSubring.mem_comap.mp hmem)
  have hval : algebraMap N Ω (algebraMap F N (y * z⁻¹)) = x * (algebraMap K Ω (ϖ : K))⁻¹ := by
    rw [map_mul, map_mul, map_inv₀, map_inv₀]
    rfl
  rw [hval] at hmem'
  exact hmem'

end InertiaPointDescent
