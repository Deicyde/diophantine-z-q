/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.Brauer.CharacterFormula), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Brauer.CharacterFormula`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Brauer.CharacterFormula
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Brauer.Archimedean.ArtinMap
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Brauer.Formation
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Brauer.OpenSubgroup
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.Character
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.FieldArtinMap
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.ArtinMap
public import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.CarryCocycle
public import ZInQKernel.Contrib.TauCeti.Backport.RepresentationTheory.Homological.ContCohomology.CarryCocycle
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.ArtinMap
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Local.ClassFormation

public section
noncomputable section

open CategoryTheory MonoidalCategory NormalLayer ContCohomology
namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- **The local character formula on an open subgroup** `inv_H (σ b ∪ δψ) = ψ (Art_L b)`. Let
`L/K` be a finite extension of nonarchimedean local fields, embedded in `Kˢ` by `σ`, so that
`H = Gal(Kˢ/σ(L))` is an open subgroup of `G_K`. For a character `ψ : H → ℚ/ℤ` with open kernel
and `b ∈ Lˣ`, if `ρ ∈ Gal(AlgebraicClosure L/L)` represents the absolute local Artin symbol
`artinMap L b`, then the invariant of `H` of the carry class of `ψ` and of the invariant `σ b` is
`ψ` of the image of `ρ` in `H` along `G_L ≃ H`. -/
theorem subgroupInvMap_characterCarryCocycle_of_mk_eq_artinMap {L : Type} [Field L]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [ValuativeExtension K L] [FiniteDimensional K L] (σ : L →ₐ[K] SeparableClosure K)
    (ψ : Additive ↥σ.fieldRange.fixingSubgroup →+ AddCircle (1 : ℚ))
    (hψ : IsOpen (ψ.ker : Set (Additive ↥σ.fieldRange.fixingSubgroup))) (b : Lˣ)
    (ρ : Field.absoluteGaloisGroup L)
    (hρ : (ρ : Field.absoluteGaloisGroupAbelianization L) = artinMap L b) :
    subgroupInvMap K σ.fieldRange.fixingSubgroup (isOpen_fixingSubgroup_fieldRange K L σ)
        (characterCarryCocycle ψ hψ (embeddedUnitsInvariants K L σ b) :
          H2 ↥σ.fieldRange.fixingSubgroup (UnitsCoeff K)) =
      ψ (.ofMul (absoluteGaloisGroupEquivFixingSubgroup K L σ
        (absoluteGaloisGroupRestrictEquiv L ρ))) := by
  let T := absoluteGaloisGroupEquivFixingSubgroup K L σ
  -- `ψ` read on `G_L` along `T`; its kernel is open.
  let χ : Additive (AbsoluteGaloisGroup L) →+ AddCircle (1 : ℚ) :=
    ψ.comp (T : AbsoluteGaloisGroup L →* ↥σ.fieldRange.fixingSubgroup).toAdditive
  have hχ : IsOpen (χ.ker : Set (Additive (AbsoluteGaloisGroup L))) := by
    rw [← AddMonoidHom.comap_ker, AddSubgroup.coe_comap]
    exact hψ.preimage (continuous_ofMul.comp (T.continuous.comp continuous_toMul))
  have hχψ : χ.comp ((T.symm : ↥σ.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup L) :
      ↥σ.fieldRange.fixingSubgroup →* AbsoluteGaloisGroup L).toAdditive = ψ :=
    AddMonoidHom.ext fun h ↦ by simp [χ]
  -- The carry class over `H` is transported from the carry class over `G_L` of `χ` and `b`.
  have hcarry : (characterCarryCocycle ψ hψ (embeddedUnitsInvariants K L σ b) :
      H2 ↥σ.fieldRange.fixingSubgroup (UnitsCoeff K)) = explicitMap2 _ _ _ _
        ((T.symm : ↥σ.fieldRange.fixingSubgroup →ₜ* AbsoluteGaloisGroup L))
        (unitsCoeffMapSymm K L σ) continuous_of_discreteTopology (unitsCoeffMapSymm_smul K L σ)
        ((unitsRepH2Equiv L).symm (unitsRepH2Equiv L
          (characterCarryCocycle χ hχ (baseUnitsEquivInvariants L (.ofMul b))))) := by
    rw [AddEquiv.symm_apply_apply, explicitMap2_characterCarryCocycle]
    congr 2
    · simp only [hχψ]
    · exact Subtype.ext ((unitsCoeffMapSymm_coe_baseUnitsEquivInvariants K L σ b).symm.trans
        (coe_explicitMap0 _ _ _ _ _ _).symm)
  rw [hcarry, subgroupInvMap_explicitMap2,
    invMap_characterCarryCocycle_of_mk_eq_artinMap χ hχ b ρ hρ]
  -- `χ` is `ψ` read along `T`.
  rfl

end TauCeti.ClassFieldTheory

open CategoryTheory MonoidalCategory NormalLayer ContCohomology
namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
open subgroup `H` of `G_K`, a character `ψ : H → ℚ/ℤ` with open kernel and `h ∈ H`, some invariant

`b ∈ ((Kˢ)ˣ)^H` has `inv_H (b ∪ δψ) = ψ(h)`. -/
theorem exists_subgroupInvMap_characterCarryCocycle_eq (H : Subgroup (AbsoluteGaloisGroup K))
    [H.FiniteIndex] (hH : IsOpen (H : Set (AbsoluteGaloisGroup K)))
    (ψ : Additive H →+ AddCircle (1 : ℚ)) (hψ : IsOpen (ψ.ker : Set (Additive H))) (h : H) :
    ∃ b : H0 H (UnitsCoeff K),
      subgroupInvMap K H hH (characterCarryCocycle ψ hψ b : H2 H (UnitsCoeff K)) =
        ψ (.ofMul h) := by
  -- `H` is the subgroup fixing its fixed field `E`, which is finite over `K`.
  obtain ⟨E, _, rfl⟩ : ∃ E : IntermediateField K (SeparableClosure K),
      FiniteDimensional K E ∧ E.val.fieldRange.fixingSubgroup = H := by
    let U : OpenSubgroup (AbsoluteGaloisGroup K) := ⟨H, hH⟩
    refine ⟨_, finiteDimensional_fixedField_toSubgroup U, ?_⟩
    rw [IntermediateField.fieldRange_val, ← toSubgroup_eq_fixingSubgroup_of_fixedField_eq rfl]
  let T := absoluteGaloisGroupEquivFixingSubgroup K E E.val
  let e := absoluteGaloisGroupRestrictEquiv E
  -- The elements on which `ψ` takes the value `ψ(h)` form an open set, `ψ` being locally constant.
  let S : Set (Field.absoluteGaloisGroup E) := {ρ | ψ (.ofMul (T (e ρ))) = ψ (.ofMul h)}
  have hS : IsOpen S := ((ψ.isLocallyConstant_of_isOpen_ker hψ).comp_continuous
    (continuous_ofMul.comp (T.continuous.comp e.continuous))).isOpen_fiber _
  have hh : e.symm (T.symm h) ∈ S := by simp [S]
  -- The canonical structure of nonarchimedean local field on `E`.
  let _ := algebraicExtensionValuativeRel K E
  let _ := algebraicExtensionNormedFieldTopology K E
  have := finiteExtension_isNonarchimedeanLocalField K E
  have := algebraicExtension_valuativeExtension K E
  obtain ⟨b, ρ, hρS, hρ⟩ := (denseRange_artinMap E).exists_mem_open
    (QuotientGroup.isOpenMap_coe _ hS) ⟨_, Set.mem_image_of_mem _ hh⟩
  exact ⟨embeddedUnitsInvariants K E E.val b,
    (subgroupInvMap_characterCarryCocycle_of_mk_eq_artinMap E.val ψ hψ b ρ hρ).trans hρS⟩

end TauCeti.ClassFieldTheory

end
end
