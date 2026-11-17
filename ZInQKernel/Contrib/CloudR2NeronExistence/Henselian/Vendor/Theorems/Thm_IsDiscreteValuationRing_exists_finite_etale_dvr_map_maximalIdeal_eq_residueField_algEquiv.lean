/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_IsDiscreteValuationRing_exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv.lean
Original Git blob: 0415d096a84ff690aeec34246aa43578dc404e50
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_IsDiscreteValuationRing_exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"

set_option autoImplicit false

universe u v

theorem IsDiscreteValuationRing.exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (k' : Type v) [Field k'] [Algebra (IsLocalRing.ResidueField R) k'] [FiniteDimensional (IsLocalRing.ResidueField R) k']
    [Algebra.IsSeparable (IsLocalRing.ResidueField R) k'] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R') (_ : Algebra R R')
      (_ : Module.Finite R R') (_ : Algebra.Etale R R') (_ : Module.FaithfullyFlat R R')
      (_ : IsLocalHom (algebraMap R R')),
      Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' ∧
      Nonempty (k' ≃ₐ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R') := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_IsDiscreteValuationRing_exists_finite_etale_dvr_map_maximalIdeal_eq_residueField_algEquiv.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
