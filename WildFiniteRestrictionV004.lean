import WildTraceV004
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Coprime periods on an actual finite Galois restriction

Restriction to a genuine finite Galois intermediate field is a continuous
finite quotient of the original field automorphism group. The inherited
valuation and the strictly small displacement condition show directly
that the restricted automorphism order is prime to every valuation-unit
prime, without assuming a ramification-group or finite-action model.
-/

noncomputable section
set_option autoImplicit false

namespace WildFiniteRestriction

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

/-- The literal scalar inclusion of the original valuation ring into its extension. -/
def valuationRingMap (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) : O →+* w :=
  ((algebraMap K Ω).comp O.subtype).codRestrict w.toSubring (fun x => by
    have hx : (x : K) ∈ w.comap (algebraMap K Ω) := hw.symm ▸ x.2
    exact hx)

/-- A valuation-unit rational prime remains a unit at the actual extension valuation. -/
theorem valuation_natCast_eq_one (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (ℓ : ℕ) (hℓ : IsUnit (ℓ : O)) :
    w.valuation (ℓ : Ω) = 1 := by
  have hu : IsUnit (ℓ : w) := by
    have h := hℓ.map (valuationRingMap O w hw)
    simpa only [map_natCast] using h
  exact (w.valuation_eq_one_iff (ℓ : w)).mp hu

/-- Actual restriction is continuous for the genuine Krull topologies. -/
theorem restriction_continuous (L : FiniteGaloisIntermediateField K Ω) :
    Continuous (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) L) :=
  InfiniteGalois.restrictNormalHom_continuous L.toIntermediateField

/-- The finite restriction has order prime to a prime invertible at the original valuation. -/
theorem restriction_order_coprime (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (ℓ : ℕ) (hℓ : ℓ.Prime) (hu : IsUnit (ℓ : O))
    (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x)
    (L : FiniteGaloisIntermediateField K Ω) :
    Nat.Coprime (orderOf (AlgEquiv.restrictNormalHom L σ)) ℓ := by
  let τ : L ≃ₐ[K] L := AlgEquiv.restrictNormalHom L σ
  let vL := w.valuation.comap L.toIntermediateField.val.toRingHom
  have hsmall : ∀ x : L, x ≠ 0 → vL (τ x - x) < vL x := by
    intro x hx
    have hxΩ : (x : Ω) ≠ 0 := fun h => hx (Subtype.ext h)
    have he : ((τ x : L) : Ω) = σ (x : Ω) :=
      AlgEquiv.restrictNormal_commutes σ L x
    change w.valuation (((τ x : L) : Ω) - (x : Ω)) < w.valuation (x : Ω)
    rw [he]
    exact hσ x hxΩ
  have hvunit : vL (ℓ : L) = 1 := by
    simpa only [vL, Valuation.comap_apply, map_natCast] using valuation_natCast_eq_one O w hw ℓ hu
  haveI : Finite (L ≃ₐ[K] L) := inferInstance
  exact WildTrace.orderOf_coprime_unit_prime vL τ hsmall (isOfFinOrder_of_finite τ) ℓ hℓ hvunit

/-- The explicit positive finite-restriction order gives an actual period on every field element.
No period or finite quotient is supplied by the caller. -/
theorem exists_restriction_coprime_period (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (ℓ : ℕ) (hℓ : ℓ.Prime) (hu : IsUnit (ℓ : O))
    (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x)
    (L : FiniteGaloisIntermediateField K Ω) :
    ∃ r : ℕ, 0 < r ∧ Nat.Coprime r ℓ ∧ ∀ x : L, (σ ^ r) (x : Ω) = (x : Ω) := by
  let τ : L ≃ₐ[K] L := AlgEquiv.restrictNormalHom L σ
  haveI : Finite (L ≃ₐ[K] L) := inferInstance
  refine ⟨orderOf τ, orderOf_pos τ, restriction_order_coprime O w hw ℓ hℓ hu σ hσ L, ?_⟩
  intro x
  have hr : AlgEquiv.restrictNormalHom L (σ ^ orderOf τ) = 1 := by
    rw [map_pow]
    exact pow_orderOf_eq_one τ
  have htx : AlgEquiv.restrictNormalHom L (σ ^ orderOf τ) x = x := by
    rw [hr]
    rfl
  have he : ((AlgEquiv.restrictNormalHom L (σ ^ orderOf τ) x : L) : Ω) =
      (σ ^ orderOf τ) (x : Ω) := AlgEquiv.restrictNormal_commutes (σ ^ orderOf τ) L x
  rw [htx] at he
  exact he.symm

end WildFiniteRestriction
