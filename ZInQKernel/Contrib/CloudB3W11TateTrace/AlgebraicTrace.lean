import Mathlib.FieldTheory.NormalizedTrace
import Mathlib.FieldTheory.Minpoly.Field

/-!
# Algebraic normalized trace retractions

This module reuses `Algebra.normalizedTrace` from Mathlib (Michal Staromiejski,
Apache-2.0) rather than defining another trace.  No continuity or uniform bound
on an infinite extension is asserted here.
-/

noncomputable section

set_option linter.style.haveILetI false

namespace ZInQ.Contrib.CloudB3W11TateTrace

open IntermediateField

section Naturality

variable {F₁ F₂ L₁ L₂ : Type*} [Field F₁] [Field F₂] [Field L₁] [Field L₂]
  [CharZero F₁] [CharZero F₂] [Algebra F₁ L₁] [Algebra F₂ L₂]
  [Algebra.IsIntegral F₁ L₁] [Algebra.IsIntegral F₂ L₂]

/-- Normalized trace is natural under simultaneous automorphisms of both fields.
This includes semilinear, not merely base-field-linear, automorphisms. -/
theorem normalizedTrace_natural (f : F₁ ≃+* F₂) (g : L₁ ≃+* L₂)
    (h : (algebraMap F₂ L₂).comp f = g.toRingHom.comp (algebraMap F₁ L₁)) (x : L₁) :
    f (Algebra.normalizedTrace F₁ L₁ x) = Algebra.normalizedTrace F₂ L₂ (g x) := by
  have hp := minpoly.map_eq_of_equiv_equiv h x
  rw [Algebra.normalizedTrace_minpoly, Algebra.normalizedTrace_minpoly, ← hp,
    Polynomial.natDegree_map_eq_of_injective f.injective, Polynomial.nextCoeff_map_eq]
  simp only [smul_eq_mul, map_mul, map_inv₀, map_natCast, map_neg]
  rfl

end Naturality

section Retractions

variable (F L : Type*) [Field F] [Field L] [CharZero F] [Algebra F L]
  [Algebra.IsIntegral F L]

/-- The genuine normalized trace to an intermediate field, embedded back in the
ambient algebraic extension.  This is an algebraic map; on all of `L` it need
not be bounded. -/
def traceRetraction (E : IntermediateField F L) : L →ₗ[F] L :=
  letI : Algebra.IsIntegral E L := Algebra.IsIntegral.tower_top F
  E.val.toLinearMap.comp ((Algebra.normalizedTrace E L).restrictScalars F)

@[simp]
theorem traceRetraction_apply (E : IntermediateField F L) (x : L) :
    traceRetraction F L E x =
      letI : Algebra.IsIntegral E L := Algebra.IsIntegral.tower_top F
      ((Algebra.normalizedTrace E L x : E) : L) := rfl

/-- The image of the algebraic retraction really lies in its target field. -/
theorem traceRetraction_mem (E : IntermediateField F L) (x : L) :
    traceRetraction F L E x ∈ E := by
  letI : Algebra.IsIntegral E L := Algebra.IsIntegral.tower_top F
  exact (Algebra.normalizedTrace E L x).property

/-- Retraction on the target field, including the infinite-extension case. -/
theorem traceRetraction_of_mem (E : IntermediateField F L) {x : L} (hx : x ∈ E) :
    traceRetraction F L E x = x := by
  letI : Algebra.IsIntegral E L := Algebra.IsIntegral.tower_top F
  let y : E := ⟨x, hx⟩
  change ((Algebra.normalizedTrace E L (algebraMap E L y) : E) : L) = x
  rw [Algebra.normalizedTrace_algebraMap_apply_eq_self]

@[simp]
theorem traceRetraction_idempotent (E : IntermediateField F L) (x : L) :
    traceRetraction F L E (traceRetraction F L E x) = traceRetraction F L E x :=
  traceRetraction_of_mem F L E (traceRetraction_mem F L E x)

/-- Higher-level traces restrict to the identity on lower levels. -/
theorem traceRetraction_of_le (E D : IntermediateField F L) (h : E ≤ D) (x : E) :
    traceRetraction F L D (x : L) = (x : L) :=
  traceRetraction_of_mem F L D (h x.property)

/-- Compatibility of normalized traces down a tower. -/
theorem traceRetraction_comp_of_le (E D : IntermediateField F L) (h : E ≤ D) (x : L) :
    traceRetraction F L E (traceRetraction F L D x) = traceRetraction F L E x := by
  letI : Algebra E D := (IntermediateField.inclusion h).toRingHom.toAlgebra
  letI : IsScalarTower E D L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI : Algebra.IsIntegral E L := Algebra.IsIntegral.tower_top F
  letI : Algebra.IsIntegral D L := Algebra.IsIntegral.tower_top F
  letI : Algebra.IsIntegral E D := Algebra.IsIntegral.tower_top F
  change ((Algebra.normalizedTrace E L
      (algebraMap D L (Algebra.normalizedTrace D L x)) : E) : L) =
    ((Algebra.normalizedTrace E L x : E) : L)
  rw [Algebra.normalizedTrace_algebraMap_apply, Algebra.normalizedTrace_trans_apply]

/-- The opposite order of the same two projections gives the lower projection. -/
theorem traceRetraction_comp_of_le' (E D : IntermediateField F L) (h : E ≤ D) (x : L) :
    traceRetraction F L D (traceRetraction F L E x) = traceRetraction F L E x :=
  traceRetraction_of_mem F L D (h (traceRetraction_mem F L E x))

/-- Galois equivariance whenever the intermediate field is stable.  Compatibility
of the two automorphisms is given explicitly, so the statement does not presume
normality of an arbitrary intermediate field. -/
theorem traceRetraction_equivariant (E : IntermediateField F L)
    (σ : L ≃ₐ[F] L) (τ : E ≃ₐ[F] E)
    (h : ∀ y : E, (τ y : L) = σ (y : L)) (x : L) :
    traceRetraction F L E (σ x) = σ (traceRetraction F L E x) := by
  letI : Algebra.IsIntegral E L := Algebra.IsIntegral.tower_top F
  have hc : (algebraMap E L).comp τ.toRingEquiv =
      σ.toRingEquiv.toRingHom.comp (algebraMap E L) := by
    ext y
    exact h y
  have ht := normalizedTrace_natural τ.toRingEquiv σ.toRingEquiv hc x
  change τ (Algebra.normalizedTrace E L x) = Algebra.normalizedTrace E L (σ x) at ht
  change ((Algebra.normalizedTrace E L (σ x) : E) : L) =
    σ ((Algebra.normalizedTrace E L x : E) : L)
  rw [← ht]
  exact h _

end Retractions

end ZInQ.Contrib.CloudB3W11TateTrace
