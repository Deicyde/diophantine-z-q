import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! faltings5-lower, part 2: superlattices of finite index (pure Mathlib). -/

set_option linter.style.haveILetI false

namespace GapHeight

open MeasureTheory Module

section Covol

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The covolume against a positive multiple of a Haar measure. -/
theorem covolume_smul_measure (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    (μ : Measure E) [μ.IsAddHaarMeasure] (c : NNReal) (hc : c ≠ 0) :
    ZLattice.covolume L (c • μ) = c * ZLattice.covolume L μ := by
  haveI : (c • μ).IsAddHaarMeasure := Measure.IsAddHaarMeasure.nnreal_smul μ hc
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L (c • μ)
      (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) (c • μ)),
    ZLattice.covolume_eq_measure_fundamentalDomain L μ
      (ZLattice.isAddFundamentalDomain (Free.chooseBasis ℤ L) μ)]
  simp [Measure.real, ENNReal.toReal_mul]

/-- **Covolume and index** for any additive Haar measure on any finite-dimensional real normed
space (Mathlib has the pi and inner-product cases): `covol L₁ = [L₂ : L₁] · covol L₂`. -/
theorem covolume_eq_relIndex_mul (μ : Measure E) [μ.IsAddHaarMeasure] (L₁ L₂ : Submodule ℤ E)
    [DiscreteTopology L₁] [IsZLattice ℝ L₁] [DiscreteTopology L₂] [IsZLattice ℝ L₂] (h : L₁ ≤ L₂) :
    ZLattice.covolume L₁ μ =
      (L₁.toAddSubgroup.relIndex L₂.toAddSubgroup : ℝ) * ZLattice.covolume L₂ μ := by
  let b := Module.finBasis ℝ E
  let f : (Fin (finrank ℝ E) → ℝ) ≃L[ℝ] E := b.equivFun.symm.toContinuousLinearEquiv
  let ν : Measure (Fin (finrank ℝ E) → ℝ) := μ.map f.symm
  haveI : ν.IsAddHaarMeasure := f.symm.isAddHaarMeasure_map μ
  have hf : MeasurePreserving f ν μ := by
    refine ⟨f.continuous.measurable, ?_⟩
    show (μ.map f.symm).map f = μ
    rw [Measure.map_map f.continuous.measurable f.symm.continuous.measurable]
    have : (f ∘ f.symm) = id := funext fun x => f.apply_symm_apply x
    rw [this, Measure.map_id]
  set c := Measure.addHaarScalarFactor ν volume
  have hν : ν = c • volume := Measure.isAddLeftInvariant_eq_smul ν volume
  have hc : c ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hν
    exact (Measure.IsAddHaarMeasure.toIsOpenPosMeasure (μ := ν)).open_pos _ isOpen_univ
      Set.univ_nonempty (by rw [hν]; rfl)
  have h1 := ZLattice.covolume_comap L₁ μ ν hf
  have h2 := ZLattice.covolume_comap L₂ μ ν hf
  rw [hν, covolume_smul_measure _ _ c hc] at h1 h2
  have hle : ZLattice.comap ℝ L₁ f.toLinearMap ≤ ZLattice.comap ℝ L₂ f.toLinearMap :=
    fun _ h' => h h'
  have key := ZLattice.covolume_div_covolume_eq_relIndex _ _ hle
  rw [ZLattice.comap_toAddSubgroup, ZLattice.comap_toAddSubgroup,
    LinearEquiv.toAddMonoidHom_commutes,
    AddSubgroup.comap_equiv_eq_map_symm', AddSubgroup.comap_equiv_eq_map_symm',
    AddSubgroup.relIndex_map_map_of_injective _ _ f.symm.injective] at key
  have hpos : 0 < ZLattice.covolume (ZLattice.comap ℝ L₂ f.toLinearMap) :=
    ZLattice.covolume_pos _ _
  rw [← h1, ← h2, ← key]
  field_simp

end Covol

section Super

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A superlattice of finite index of a full lattice is a full lattice (discreteness). -/
theorem discreteTopology_of_le_of_relIndex (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] (hi : L₁.toAddSubgroup.relIndex L₂.toAddSubgroup ≠ 0) : DiscreteTopology L₂ := by
  set d := L₁.toAddSubgroup.relIndex L₂.toAddSubgroup
  have hmem : ∀ x : L₂, d • (x : E) ∈ L₁ := fun x =>
    L₁.toAddSubgroup.nsmul_relIndex_mem (K := L₂.toAddSubgroup) (g := (x : E)) x.2
  let m : L₂ → L₁ := fun x => ⟨d • (x : E), hmem x⟩
  have hm : Continuous m :=
    Continuous.subtype_mk ((continuous_const_smul _).comp continuous_subtype_val) _
  have hinj : Function.Injective m := by
    intro x y hxy
    have h1 : d • (x : E) = d • (y : E) := congrArg Subtype.val hxy
    have hd : (d : ℝ) ≠ 0 := by exact_mod_cast hi
    have h2 : (d : ℝ) • (x : E) = (d : ℝ) • (y : E) := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
      exact h1
    exact Subtype.ext (smul_right_injective E hd h2)
  exact DiscreteTopology.of_continuous_injective hm hinj

theorem isZLattice_of_le (L₁ L₂ : Submodule ℤ E) [DiscreteTopology L₁] [IsZLattice ℝ L₁]
    [DiscreteTopology L₂] (h : L₁ ≤ L₂) :
    IsZLattice ℝ L₂ where
  span_top := by
    rw [eq_top_iff, ← IsZLattice.span_top (K := ℝ) (L := L₁)]
    exact Submodule.span_mono h

end Super

end GapHeight
