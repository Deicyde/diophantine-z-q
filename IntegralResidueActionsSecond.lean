import OriginalPointBindingFirst

/-!
# Covariance of the actual integral reduction under decomposition automorphisms

The native valuation-ring action descends along the actual residue quotient.
Its Spec map therefore commutes with the actual integral reduction arrow.
Separatedness and the original generic-point Galois action then imply that
a fixed original point has a fixed native residue point.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace SemistableGeometry.IntegralResidueActions

open SemistableGeometry.IntegralGalois
open SemistableGeometry.OriginalPointBinding

variable {K : Type} [Field K] {O : ValuationSubring K}
variable {Ω : Type} [Field Ω] [Algebra K Ω]

/-- The residue action is the native decomposition-group ring automorphism action. -/
def residueRingAction (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω)
    (hD : σ ∈ w.decompositionSubgroup K) : IsLocalRing.ResidueField w →+* IsLocalRing.ResidueField w :=
  (MulSemiringAction.toRingAut (w.decompositionSubgroup K) (IsLocalRing.ResidueField w) ⟨σ, hD⟩).toRingHom

/-- The actual ring action descends along the actual residue map. -/
theorem residueRingAction_residue (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω)
    (hD : σ ∈ w.decompositionSubgroup K) :
    (residueRingAction w σ hD).comp (IsLocalRing.residue w) =
      (IsLocalRing.residue w).comp (valuationAction w σ hD) := by
  ext a
  change (⟨σ, hD⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w a =
    IsLocalRing.residue w ((⟨σ, hD⟩ : w.decompositionSubgroup K) • a)
  rw [← IsLocalRing.ResidueField.residue_smul]

/-- The actual residue action preserves the given original integral base. -/
theorem residueRingAction_base (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K) :
    (residueRingAction w σ hD).comp ((IsLocalRing.residue w).comp (PkgI2.toW O w hw)) =
      (IsLocalRing.residue w).comp (PkgI2.toW O w hw) := by
  rw [← RingHom.comp_assoc, residueRingAction_residue, RingHom.comp_assoc, valuationAction_base]

/-- The native residue Spec action, as an actual morphism over the original base. -/
def residueActionArrow (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K) :
    residueDomain w hw ⟶ residueDomain w hw :=
  Over.homMk (Spec.map (CommRingCat.ofHom (residueRingAction w σ hD))) (by
    change Spec.map (CommRingCat.ofHom (residueRingAction w σ hD)) ≫
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue w).comp (PkgI2.toW O w hw))) =
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue w).comp (PkgI2.toW O w hw)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, residueRingAction_base])

/-- Reduction covariance uses the genuine native Spec orientations. -/
theorem reductionArrow_covariance (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K) :
    residueActionArrow w hw σ hD ≫ reductionArrow w hw =
      reductionArrow w hw ≫ valuationActionArrow w hw σ hD := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (residueRingAction w σ hD)) ≫
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) =
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue w)) ≫
      Spec.map (CommRingCat.ofHom (valuationAction w σ hD))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    residueRingAction_residue]

/-- A fixed original generic point yields an actual fixed native residue section. -/
theorem reduction_fixed_of_original_fixed {A : PkgI3.AbVar K}
    (N : Over (Spec (CommRingCat.of O))) [IsSeparated N.hom]
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
    (a : valuationDomain w hw ⟶ N)
    (hfix : A.galAct σ (originalPoint N gen w hw a) = originalPoint N gen w hw a) :
    residueActionArrow w hw σ hD ≫ (reductionArrow w hw ≫ a) = reductionArrow w hw ≫ a := by
  rw [← Category.assoc, reductionArrow_covariance, Category.assoc,
    integral_fixed_of_original_fixed N gen w hw σ hD a hfix]

end SemistableGeometry.IntegralResidueActions
