import ActualInertiaRestrictionV002

/-!
# Strict displacement elements lie in the actual inertia group

The strict inequality preserves the valuation and kills every residue
class. It therefore implies inertia in the original valuation-ring
kernel, without an extra inertia assumption.
-/

noncomputable section
set_option autoImplicit false
open scoped Pointwise

namespace ActualInertiaRestriction
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

lemma strict_implies_inertia (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ x : Ω, x ≠ 0 → w.valuation (σ x - x) < w.valuation x) :
    PkgI2.IsInertia w σ := by
  have hD : σ ∈ w.decompositionSubgroup K := by
    apply (decomposition_iff w σ).mpr
    intro x
    rw [← w.valuation_le_one_iff, ← w.valuation_le_one_iff,
      WildTrace.valuation_apply_eq w.valuation σ hσ x]
  refine ⟨hD, (inertia_iff_residue_fixed w σ hD).mpr ?_⟩
  intro a
  apply sub_eq_zero.mp
  rw [← map_sub, IsLocalRing.residue_eq_zero_iff]
  apply (w.valuation_lt_one_iff _).mpr
  change w.valuation (σ (a : Ω) - (a : Ω)) < 1
  by_cases ha : (a : Ω) = 0
  · simp [ha]
  · exact (hσ a ha).trans_le (w.valuation_le_one a)

lemma strictGroup_le_inertia (w : ValuationSubring Ω) :
    WildFiniteGroup.strictDisplacementGroup (K := K) w ≤ inertiaGroup (K := K) w := by
  intro σ hσ
  exact (mem_inertiaGroup w σ).mpr (strict_implies_inertia w σ hσ)

lemma wildImage_le_inertiaImage (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω) :
    ActualFiniteRamification.wildImage w L ≤
      (inertiaGroup (K := K) w).map (AlgEquiv.restrictNormalHom L) :=
  Subgroup.map_mono (strictGroup_le_inertia w)

end ActualInertiaRestriction
