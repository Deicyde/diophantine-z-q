import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Definitions/Def_AlgebraicGeometry_MazurRapoportAppendixGenericFibreOpenImmersionDVR.lean
Original Git blob: 3c1f10329cbf026dfbd1a53b841ac1b758be8107
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 13 namespace-sensitive axiom-print diagnostics; full final AX3 audit is separate.
-/
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.SharedDiagnostics
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace NeronModelInfra
h77_bridge_namespace

section RingSide

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

theorem isLocalizationAway_of_irreducible {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalization.Away ϖ K := by
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers ϖ)
      (nonZeroDivisors R) ?_ ?_).mpr inferInstance
  · intro x hx
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff x ϖ).mp hx
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n hϖ.ne_zero)
  · intro r hr
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (nonZeroDivisors.ne_zero hr) hϖ
    exact ⟨ϖ ^ n, (Submonoid.mem_powers_iff _ ϖ).mpr ⟨n, rfl⟩, hn.dvd⟩

instance isLocalizationAway_uniformizer_zp (p : ℕ) [Fact p.Prime] :
    IsLocalization.Away (p : ℤ_[p]) ℚ_[p] :=
  isLocalizationAway_of_irreducible ℚ_[p] (PadicInt.irreducible_p (p := p))

theorem isLocalizationAway_uniformizer_three :
    IsLocalization.Away (3 : ℤ_[3]) ℚ_[3] := by
  simpa using isLocalizationAway_uniformizer_zp 3

end RingSide

section SchemeSide

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]

instance isOpenImmersion_specGenericFibreInclusion :
    IsOpenImmersion (specGenericFibreInclusion R K) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  haveI : IsLocalization.Away ϖ K := isLocalizationAway_of_irreducible K hϖ
  rw [specGenericFibreInclusion_eq]
  exact AlgebraicGeometry.IsOpenImmersion.of_isLocalization ϖ

theorem range_specGenericFibreInclusion_eq_basicOpen {ϖ : R} (hϖ : Irreducible ϖ) :
    Set.range (specGenericFibreInclusion R K).base =
      (PrimeSpectrum.basicOpen ϖ : Set (PrimeSpectrum R)) := by
  haveI : IsLocalization.Away ϖ K := isLocalizationAway_of_irreducible K hϖ
  have h := PrimeSpectrum.localization_away_comap_range K ϖ
  rw [specGenericFibreInclusion_eq]
  exact h

theorem mono_specGenericFibreInclusion_of_dvr :
    Mono (specGenericFibreInclusion R K) :=
  inferInstance

theorem flat_specGenericFibreInclusion_of_dvr :
    Flat (specGenericFibreInclusion R K) :=
  inferInstance

end SchemeSide

section PadicGates

theorem gate_isOpenImmersion_specGenericFibreInclusion_zp (p : ℕ) [Fact p.Prime] :
    IsOpenImmersion (specGenericFibreInclusion ℤ_[p] ℚ_[p]) :=
  isOpenImmersion_specGenericFibreInclusion ℤ_[p] ℚ_[p]

theorem gate_isOpenImmersion_specGenericFibreInclusion_three :
    IsOpenImmersion (specGenericFibreInclusion ℤ_[3] ℚ_[3]) :=
  gate_isOpenImmersion_specGenericFibreInclusion_zp 3

theorem not_isIso_specGenericFibreInclusion_zp (p : ℕ) [Fact p.Prime] :
    ¬ IsIso (specGenericFibreInclusion ℤ_[p] ℚ_[p]) := by
  intro h
  exact (isEmpty_schemeHomOver_id_specGenericFibreInclusion_zp p).false
    ⟨inv (specGenericFibreInclusion ℤ_[p] ℚ_[p]),
      IsIso.inv_hom_id (specGenericFibreInclusion ℤ_[p] ℚ_[p])⟩

theorem not_isIso_specGenericFibreInclusion_three :
    ¬ IsIso (specGenericFibreInclusion ℤ_[3] ℚ_[3]) :=
  not_isIso_specGenericFibreInclusion_zp 3

theorem gate_strictOpenImmersion_specGenericFibreInclusion_zp (p : ℕ) [Fact p.Prime] :
    IsOpenImmersion (specGenericFibreInclusion ℤ_[p] ℚ_[p]) ∧
      ¬ IsIso (specGenericFibreInclusion ℤ_[p] ℚ_[p]) :=
  ⟨gate_isOpenImmersion_specGenericFibreInclusion_zp p,
    not_isIso_specGenericFibreInclusion_zp p⟩

theorem gate_strictOpenImmersion_specGenericFibreInclusion_three :
    IsOpenImmersion (specGenericFibreInclusion ℤ_[3] ℚ_[3]) ∧
      ¬ IsIso (specGenericFibreInclusion ℤ_[3] ℚ_[3]) :=
  gate_strictOpenImmersion_specGenericFibreInclusion_zp 3

end PadicGates

end NeronModelInfra














end


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
