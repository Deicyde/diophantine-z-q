import InertiaFromIntegralV001

/-!
# The integral closure of the base valuation ring in `Ω`, its Galois action and center

For a discrete valuation subring `O` of `K` and an algebraic extension `Ω/K`:

* `intClosure O` is the subring of elements of `Ω` integral over `O`;
* `K`-automorphisms of `Ω` act on it (`MulSemiringAction`);
* for a valuation subring `w` of `Ω` above `O`, `centerIdeal O w hw` is the prime of `intClosure O`
  of elements in the maximal ideal of `w`;
* every element of the inertia group of `centerIdeal` (ring-theoretic inertia for the action) lies in
  the inertia subgroup of `w` (`mem_inertia_of_mem_inertia_centerIdeal`).
-/

noncomputable section
set_option autoImplicit false

namespace InertiaPointDescent

open scoped Pointwise

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- Elements of `Ω` integral over `O`, as a subring. -/
def intClosure (O : ValuationSubring K) : Subring Ω :=
  letI : Algebra O Ω := ((algebraMap K Ω).comp (algebraMap O K)).toAlgebra
  (integralClosure O Ω).toSubring

theorem mem_intClosure_iff (O : ValuationSubring K) (s : Ω) :
    s ∈ intClosure (Ω := Ω) O ↔ IntegralOver O s :=
  Iff.rfl

theorem integralOver_map (O : ValuationSubring K) (σ : Ω ≃ₐ[K] Ω) {s : Ω}
    (hs : IntegralOver O s) : IntegralOver O (σ s) := by
  let _ : Algebra O Ω := ((algebraMap K Ω).comp (algebraMap O K)).toAlgebra
  have : IsScalarTower O K Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have h : IsIntegral O s := hs
  exact IsIntegral.map (σ.toAlgHom.restrictScalars O) h

instance (O : ValuationSubring K) : MulSemiringAction (Ω ≃ₐ[K] Ω) (intClosure (Ω := Ω) O) where
  smul σ s := ⟨σ (s : Ω), integralOver_map (Ω := Ω) O σ (s := (s : Ω)) s.2⟩
  one_smul s := Subtype.ext rfl
  mul_smul σ τ s := Subtype.ext rfl
  smul_zero σ := Subtype.ext (show σ (0 : Ω) = 0 from map_zero σ)
  smul_add σ s t := Subtype.ext (show σ ((s : Ω) + t) = σ s + σ t from map_add σ _ _)
  smul_one σ := Subtype.ext (show σ (1 : Ω) = 1 from map_one σ)
  smul_mul σ s t := Subtype.ext (show σ ((s : Ω) * t) = σ s * σ t from map_mul σ _ _)

theorem coe_smul_intClosure (O : ValuationSubring K) (σ : Ω ≃ₐ[K] Ω)
    (s : intClosure (Ω := Ω) O) :
    ((σ • s : intClosure (Ω := Ω) O) : Ω) = σ (s : Ω) :=
  rfl

/-- The center of `w` on `intClosure O`. -/
def centerIdeal (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) : Ideal (intClosure (Ω := Ω) O) :=
  (IsLocalRing.maximalIdeal w).comap
    ((Subring.subtype (intClosure (Ω := Ω) O)).codRestrict w.toSubring
      (fun s => mem_of_integralOver O w hw (s := (s : Ω)) s.2))

theorem mem_centerIdeal_iff (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (s : intClosure (Ω := Ω) O) :
    s ∈ centerIdeal O w hw ↔ w.valuation (s : Ω) < 1 := by
  unfold centerIdeal
  rw [Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
  rfl

instance (O : ValuationSubring K) (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O) :
    (centerIdeal O w hw).IsPrime := by
  unfold centerIdeal
  exact Ideal.comap_isPrime _ _

/-- **Ring-theoretic inertia of the center gives valuation-theoretic inertia of `w`.** -/
theorem mem_inertia_of_mem_inertia_centerIdeal [CharZero K] [Algebra.IsAlgebraic K Ω]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (σ : Ω ≃ₐ[K] Ω)
    (hσ : σ ∈ (centerIdeal O w hw).inertia (Ω ≃ₐ[K] Ω)) :
    ∃ h : σ ∈ w.decompositionSubgroup K,
      (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K := by
  refine mem_inertia_of_integral O w hw σ (fun s hs => ?_)
  have h := hσ ⟨s, hs⟩
  rw [Submodule.mem_toAddSubgroup, mem_centerIdeal_iff] at h
  exact h

end InertiaPointDescent
