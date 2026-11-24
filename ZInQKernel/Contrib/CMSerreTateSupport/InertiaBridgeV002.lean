import ZInQKernel.Contrib.CMSerreTateSupport.ActualTameQuotientV003
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The actual inertia subgroup is Mathlib's inertia subgroup; finite-layer compatibility

* `mem_inertiaGroup_iff_inertiaSubgroup`: on an algebraic extension, `σ ∈ inertiaGroup w` (trivial
  action on residues of `w`) iff `σ` lies in the decomposition subgroup of `w` and its image lies
  in Mathlib's `ValuationSubring.inertiaSubgroup`, the kernel of the action on the residue field.
* `layerRestrict_mem_inertiaGroup`, `layerRestrict_mem_inertiaSubgroup`: restriction of an
  actual inertia element to a finite Galois layer `L` is an inertia element of `w ∩ L` in
  `Gal(L/K)`, in both forms.
* `layerRestrict_mem_wildGroup`: restriction of an actual wild element is wild for `w ∩ L`.
* `layerRestrict_preserves`: restriction preserves the valuation of `w ∩ L`.

No surjectivity of restriction on inertia or wild inertia is claimed.
-/

noncomputable section
set_option autoImplicit false

namespace ActualTameInertia

open scoped Pointwise

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem residue_lt_one_of_mem_inertiaSubgroup {w : ValuationSubring Ω} {σ : Ω ≃ₐ[K] Ω}
    (h : σ ∈ w.decompositionSubgroup K)
    (hI : (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K) (u : Ω) (hu : u ∈ w) :
    w.valuation (σ u - u) < 1 := by
  have h1 : MulSemiringAction.toRingAut (w.decompositionSubgroup K)
      (IsLocalRing.ResidueField w) ⟨σ, h⟩ = 1 := hI
  have h2 : (⟨σ, h⟩ : w.decompositionSubgroup K) • IsLocalRing.residue w ⟨u, hu⟩ =
      IsLocalRing.residue w ⟨u, hu⟩ := by
    have := congrArg (fun e => e (IsLocalRing.residue w ⟨u, hu⟩)) h1
    exact this
  rw [← IsLocalRing.ResidueField.residue_smul] at h2
  have h3 : (⟨σ, h⟩ : w.decompositionSubgroup K) • (⟨u, hu⟩ : w) - ⟨u, hu⟩ ∈
      IsLocalRing.maximalIdeal w := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h2, sub_self]
  rw [ValuationSubring.valuation_lt_one_iff] at h3
  exact h3

theorem mem_decompositionSubgroup_of_mem_inertiaGroup [Algebra.IsAlgebraic K Ω]
    {w : ValuationSubring Ω} {σ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ inertiaGroup w) :
    σ ∈ w.decompositionSubgroup K := by
  rw [MulAction.mem_stabilizer_iff]
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact apply_mem_iff (inv_mem hσ) y

theorem mem_inertiaSubgroup_of_mem_inertiaGroup [Algebra.IsAlgebraic K Ω]
    {w : ValuationSubring Ω} {σ : Ω ≃ₐ[K] Ω} (hσ : σ ∈ inertiaGroup w) :
    (⟨σ, mem_decompositionSubgroup_of_mem_inertiaGroup hσ⟩ : w.decompositionSubgroup K) ∈
      w.inertiaSubgroup K := by
  show MulSemiringAction.toRingAut (w.decompositionSubgroup K) (IsLocalRing.ResidueField w)
    ⟨σ, mem_decompositionSubgroup_of_mem_inertiaGroup hσ⟩ = 1
  ext r
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
  show (⟨σ, mem_decompositionSubgroup_of_mem_inertiaGroup hσ⟩ : w.decompositionSubgroup K) •
    IsLocalRing.residue w a = IsLocalRing.residue w a
  rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
    IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
  exact (mem_inertiaGroup_iff.1 hσ) a a.2

/-- **The actual inertia subgroup is Mathlib's inertia subgroup** (decomposition subgroup, then
kernel of the action on the residue field), on an algebraic extension. -/
theorem mem_inertiaGroup_iff_inertiaSubgroup [Algebra.IsAlgebraic K Ω] (w : ValuationSubring Ω)
    (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ inertiaGroup w ↔ ∃ h : σ ∈ w.decompositionSubgroup K,
      (⟨σ, h⟩ : w.decompositionSubgroup K) ∈ w.inertiaSubgroup K :=
  ⟨fun hσ => ⟨_, mem_inertiaSubgroup_of_mem_inertiaGroup hσ⟩,
    fun ⟨h, hI⟩ => mem_inertiaGroup_iff.2 (residue_lt_one_of_mem_inertiaSubgroup h hI)⟩

/-! ### Finite-layer compatibility of restriction -/

section Layer

variable [IsGalois K Ω] (w : ValuationSubring Ω) (L : FiniteGaloisIntermediateField K Ω)

/-- The valuation ring `w ∩ L` of the finite layer. -/
abbrev layerRing : ValuationSubring L.toIntermediateField :=
  w.comap (algebraMap L.toIntermediateField Ω)

theorem layerRing_comap {O : ValuationSubring K} (hw : w.comap (algebraMap K Ω) = O) :
    (layerRing w L).comap (algebraMap K L.toIntermediateField) = O := by
  rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hw]

/-- Restriction preserves the valuation of the finite layer. -/
theorem layerRestrict_preserves (σ : inertiaGroup (K := K) w) (x : L.toIntermediateField) :
    (layerRing w L).valuation (layerRestrict w L σ x) = (layerRing w L).valuation x := by
  have hequiv := comap_valuation_isEquiv (algebraMap L.toIntermediateField Ω) w
  rw [hequiv.eq_iff, Valuation.comap_apply, Valuation.comap_apply]
  change w.valuation (((layerRestrict w L σ x : L.toIntermediateField) : Ω)) = w.valuation (x : Ω)
  rw [layerRestrict_apply]
  exact preserves σ.2 (x : Ω)

/-- Restriction of an actual inertia element is an inertia element of the finite layer. -/
theorem layerRestrict_mem_inertiaGroup (σ : inertiaGroup (K := K) w) :
    layerRestrict w L σ ∈ inertiaGroup (K := K) (layerRing w L) := by
  have hequiv := comap_valuation_isEquiv (algebraMap L.toIntermediateField Ω) w
  rw [mem_inertiaGroup_iff]
  intro u hu
  rw [hequiv.lt_one_iff_lt_one, Valuation.comap_apply, map_sub]
  change w.valuation (((layerRestrict w L σ u : L.toIntermediateField) : Ω) - (u : Ω)) < 1
  rw [layerRestrict_apply]
  exact (mem_inertiaGroup_iff.1 σ.2) (u : Ω) (ValuationSubring.mem_comap.1 hu)

/-- The same, in Mathlib's decomposition/inertia form for the finite layer. -/
theorem layerRestrict_mem_inertiaSubgroup (σ : inertiaGroup (K := K) w) :
    ∃ h : layerRestrict w L σ ∈ (layerRing w L).decompositionSubgroup K,
      (⟨layerRestrict w L σ, h⟩ : (layerRing w L).decompositionSubgroup K) ∈
        (layerRing w L).inertiaSubgroup K :=
  (mem_inertiaGroup_iff_inertiaSubgroup _ _).1 (layerRestrict_mem_inertiaGroup w L σ)

/-- Restriction of an actual wild element is wild for the finite layer. -/
theorem layerRestrict_mem_wildGroup (σ : inertiaGroup (K := K) w)
    (hσ : (σ : Ω ≃ₐ[K] Ω) ∈ wildGroup w) :
    layerRestrict w L σ ∈ wildGroup (K := K) (layerRing w L) := by
  have hequiv := comap_valuation_isEquiv (algebraMap L.toIntermediateField Ω) w
  rw [mem_wildGroup_iff]
  intro x hx
  have hxΩ : (x : Ω) ≠ 0 := fun h => hx (Subtype.ext h)
  rw [hequiv.lt_iff_lt, Valuation.comap_apply, Valuation.comap_apply, map_sub]
  change w.valuation (((layerRestrict w L σ x : L.toIntermediateField) : Ω) - (x : Ω)) <
    w.valuation (x : Ω)
  rw [layerRestrict_apply]
  exact mem_wildGroup_iff.1 hσ (x : Ω) hxΩ

end Layer

end ActualTameInertia

#print axioms ActualTameInertia.mem_inertiaGroup_iff_inertiaSubgroup
#print axioms ActualTameInertia.layerRestrict_mem_inertiaSubgroup
#print axioms ActualTameInertia.layerRestrict_mem_wildGroup
#print axioms ActualTameInertia.layerRestrict_preserves
