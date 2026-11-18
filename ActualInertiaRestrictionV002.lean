import ActualDivisionFieldV004
import ActualFiniteRamificationV002

/-!
# Restriction of actual inertia to a finite Galois field

Inertia is the genuine kernel on the residue field of the given valuation
ring. Restriction preserves this condition on the inverse-image ring,
not only an abstract isomorphic representation.
-/

noncomputable section
set_option autoImplicit false
open scoped Pointwise

namespace ActualInertiaRestriction
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

lemma decomposition_iff (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ w.decompositionSubgroup K ↔ ∀ x : Ω, σ x ∈ w ↔ x ∈ w := by
  change σ • w = w ↔ _
  constructor
  · intro h x
    have hx := ValuationSubring.smul_mem_pointwise_smul_iff (g := σ) (S := w) (x := x)
    rw [h] at hx
    exact hx
  · intro h
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have hx := h (σ⁻¹ x)
    have he : σ (σ⁻¹ x) = x := by
      rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
    rw [he] at hx
    exact hx.symm

lemma restrict_decomposition (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω)
    (σ : Ω ≃ₐ[K] Ω) (hσ : σ ∈ w.decompositionSubgroup K) :
    AlgEquiv.restrictNormalHom L σ ∈
      (w.comap L.toIntermediateField.val.toRingHom).decompositionSubgroup K := by
  apply (decomposition_iff _ _).mpr
  intro x
  have he : ((AlgEquiv.restrictNormalHom L σ x : L) : Ω) = σ (x : Ω) :=
    AlgEquiv.restrictNormal_commutes σ L x
  change (((AlgEquiv.restrictNormalHom L σ x : L) : Ω) ∈ w) ↔ (x : Ω) ∈ w
  rw [he]
  exact (decomposition_iff w σ).mp hσ x

lemma inertia_residue_fixed (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω)
    (hσ : σ ∈ w.decompositionSubgroup K)
    (hI : (⟨σ, hσ⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K) (a : w) :
    IsLocalRing.residue w ((⟨σ, hσ⟩ : w.decompositionSubgroup K) • a) = IsLocalRing.residue w a := by
  change MulSemiringAction.toRingAut (w.decompositionSubgroup K) (IsLocalRing.ResidueField w)
    (⟨σ, hσ⟩ : w.decompositionSubgroup K) = 1 at hI
  have h := congrArg (fun e : RingAut (IsLocalRing.ResidueField w) => e (IsLocalRing.residue w a)) hI
  exact h

lemma inertia_iff_residue_fixed (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω)
    (hσ : σ ∈ w.decompositionSubgroup K) :
    (⟨σ, hσ⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K ↔
      ∀ a : w, IsLocalRing.residue w ((⟨σ, hσ⟩ : w.decompositionSubgroup K) • a) =
        IsLocalRing.residue w a := by
  constructor
  · exact inertia_residue_fixed w σ hσ
  · intro h
    change MulSemiringAction.toRingAut (w.decompositionSubgroup K) (IsLocalRing.ResidueField w)
      (⟨σ, hσ⟩ : w.decompositionSubgroup K) = 1
    apply RingEquiv.ext
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    exact h a

def valuationInclusion (w : ValuationSubring Ω) (L : IntermediateField K Ω) :
    (w.comap L.val.toRingHom) →+* w :=
  (L.val.toRingHom.comp (w.comap L.val.toRingHom).subtype).codRestrict w.toSubring (fun a => a.2)

instance valuationInclusion_local (w : ValuationSubring Ω) (L : IntermediateField K Ω) :
    IsLocalHom (valuationInclusion w L) := by
  constructor
  intro a ha
  apply ((w.comap L.val.toRingHom).valuation_eq_one_iff a).mpr
  apply (ActualFiniteRamification.valuation_comap_equiv w L).eq_one_iff_eq_one.mp
  exact (w.valuation_eq_one_iff (valuationInclusion w L a)).mp ha

lemma restrict_inertia (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω)
    (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) :
    PkgI2.IsInertia (w.comap L.toIntermediateField.val.toRingHom)
      (AlgEquiv.restrictNormalHom L σ) := by
  obtain ⟨hD, hI⟩ := hσ
  let wL := w.comap L.toIntermediateField.val.toRingHom
  have hDL := restrict_decomposition w L σ hD
  refine ⟨hDL, (inertia_iff_residue_fixed wL _ hDL).mpr ?_⟩
  intro a
  let f := IsLocalRing.ResidueField.map (valuationInclusion w L.toIntermediateField)
  apply f.injective
  change IsLocalRing.residue w
    (valuationInclusion w L.toIntermediateField ((⟨AlgEquiv.restrictNormalHom L σ, hDL⟩ : wL.decompositionSubgroup K) • a)) =
      IsLocalRing.residue w (valuationInclusion w L.toIntermediateField a)
  have he : valuationInclusion w L.toIntermediateField
      ((⟨AlgEquiv.restrictNormalHom L σ, hDL⟩ : wL.decompositionSubgroup K) • a) =
      (⟨σ, hD⟩ : w.decompositionSubgroup K) • valuationInclusion w L.toIntermediateField a := by
    apply Subtype.ext
    exact AlgEquiv.restrictNormal_commutes σ L a.1
  rw [he]
  exact inertia_residue_fixed w σ hD hI _

def inertiaGroup (w : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[K] Ω) :=
  (w.inertiaSubgroup K).map (w.decompositionSubgroup K).subtype

lemma mem_inertiaGroup (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ inertiaGroup (K := K) w ↔ PkgI2.IsInertia w σ := by
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨τ.2, hτ⟩
  · rintro ⟨hD, hI⟩
    exact ⟨⟨σ, hD⟩, hI, rfl⟩

lemma inertiaImage_le (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω) :
    (inertiaGroup (K := K) w).map (AlgEquiv.restrictNormalHom L) ≤
      inertiaGroup (K := K) (w.comap L.toIntermediateField.val.toRingHom) := by
  rintro τ ⟨σ, hσ, rfl⟩
  exact (mem_inertiaGroup _ _).mpr (restrict_inertia w L σ ((mem_inertiaGroup w σ).mp hσ))

end ActualInertiaRestriction
