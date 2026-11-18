import ValuationCenterV001
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Valuation.Integral

/-!
# Decomposition is determined by the center on integral elements

Let `O` be a discrete valuation subring of a field `K` of characteristic zero, `Ω/K` algebraic, and
`w` a valuation subring of `Ω` with `w ∩ K = O`. If a `K`-automorphism `σ` of `Ω` preserves the
center of `w` on elements integral over `O` (an integral element is a nonunit of `w` exactly when
its image is), then `σ` preserves `w`, i.e. lies in the decomposition subgroup of `w`.

Proof: for `x ∈ Ω` let `N = K(x)` and `B` the integral closure of `O` in `N` (a Dedekind domain
with fraction field `N`). The valuation subrings `w ∩ N` and `σ⁻¹(w) ∩ N` of `N` contain `B` and
have the same center on `B`, hence are equal; so `x ∈ w ↔ σ x ∈ w`.
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

open scoped Pointwise

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- Integrality over a valuation subring `O` of the base field. -/
def IntegralOver (O : ValuationSubring K) (s : Ω) : Prop :=
  ((algebraMap K Ω).comp (algebraMap O K)).IsIntegralElem s

/-- Membership of a comap valuation subring's nonunits. -/
theorem comap_valuation_lt_one_iff {N : Type*} [Field N] (W : ValuationSubring Ω) (f : N →+* Ω)
    (y : N) : (W.comap f).valuation y < 1 ↔ W.valuation (f y) < 1 := by
  rw [← ValuationSubring.mem_nonunits_iff, ← ValuationSubring.mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap, map_inv₀, map_eq_zero_iff f f.injective]

/-- An element integral over `O` lies in every valuation subring above `O`. -/
theorem mem_of_integralOver (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) {s : Ω} (hs : IntegralOver O s) : s ∈ w := by
  let φ : O →+* w := ((algebraMap K Ω).comp (algebraMap O K)).codRestrict w.toSubring
    (fun c => by
      have hc : (c : K) ∈ w.comap (algebraMap K Ω) := by rw [hw]; exact c.2
      exact hc)
  let _ : Algebra O w := φ.toAlgebra
  let _ : Algebra O Ω := ((algebraMap K Ω).comp (algebraMap O K)).toAlgebra
  have : IsScalarTower O w Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h1 : IsIntegral O s := hs
  have h2 : IsIntegral w s := h1.tower_top
  have hv : Valuation.Integers w.valuation w :=
    ⟨Subtype.val_injective, fun x => w.valuation_le_one x,
      fun r hr => ⟨⟨r, (w.valuation_le_one_iff r).1 hr⟩, rfl⟩⟩
  exact (w.valuation_le_one_iff s).1 (hv.mem_of_integral h2)

/-- **An automorphism preserving the center on integral elements preserves `w`.** -/
theorem mem_iff_of_center [CharZero K] [Algebra.IsAlgebraic K Ω] (O : ValuationSubring K)
    [IsDiscreteValuationRing O] (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ s : Ω, IntegralOver O s → (w.valuation s < 1 ↔ w.valuation (σ s) < 1))
    (x : Ω) : x ∈ w ↔ σ x ∈ w := by
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
  let f₂ : N →+* Ω := (σ : Ω →+* Ω).comp N.val.toRingHom
  let W₁ := w.comap f₁
  let W₂ := w.comap f₂
  -- integral elements of `N` map to integral elements of `Ω`
  have hint : ∀ b : B, IntegralOver O ((b : N) : Ω) := by
    intro b
    have hb : IsIntegral O (b : N) := b.2
    have := hb.map (N.val.restrictScalars O)
    exact this
  have hintσ : ∀ b : B, IntegralOver O (σ ((b : N) : Ω)) := by
    intro b
    have := IsIntegral.map (σ.toAlgHom.restrictScalars O) (hint b : IsIntegral O ((b : N) : Ω))
    exact this
  have h₁ : ∀ b : B, algebraMap B N b ∈ W₁ := fun b =>
    ValuationSubring.mem_comap.mpr (mem_of_integralOver O w hw (hint b))
  have h₂ : ∀ b : B, algebraMap B N b ∈ W₂ := fun b =>
    ValuationSubring.mem_comap.mpr (mem_of_integralOver O w hw (hintσ b))
  have hc : center W₁ h₁ = center W₂ h₂ := by
    ext b
    rw [mem_center_iff, mem_center_iff, comap_valuation_lt_one_iff, comap_valuation_lt_one_iff]
    exact hσ _ (hint b)
  have heq := eq_of_center_eq W₁ W₂ h₁ h₂ hc
  have hxN : x ∈ N := IntermediateField.mem_adjoin_simple_self K x
  have key : (⟨x, hxN⟩ : N) ∈ W₁ ↔ (⟨x, hxN⟩ : N) ∈ W₂ := by rw [heq]
  exact key

/-- **Decomposition subgroup membership from the center on integral elements.** -/
theorem mem_decompositionSubgroup_of_center [CharZero K] [Algebra.IsAlgebraic K Ω]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ s : Ω, IntegralOver O s → (w.valuation s < 1 ↔ w.valuation (σ s) < 1)) :
    σ ∈ w.decompositionSubgroup K := by
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have h := mem_iff_of_center O w hw σ hσ (σ⁻¹ • x)
  rw [h]
  change σ (σ⁻¹ x) ∈ w ↔ x ∈ w
  rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

end InertiaPointDescent
