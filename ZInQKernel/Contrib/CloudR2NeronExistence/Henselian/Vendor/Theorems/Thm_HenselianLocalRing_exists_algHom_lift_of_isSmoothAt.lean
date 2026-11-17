import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Theorems/Thm_HenselianLocalRing_exists_algHom_lift_of_isSmoothAt.lean
Original Git blob: 6c608e861b5f85d183441189dac523eceef7ce99
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.Sol.S_HenselianLocalRing_exists_algHom_lift_of_isSmoothAt

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

universe u

theorem HenselianLocalRing.exists_algHom_lift_of_isSmoothAt
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    (S : Type u) [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    (φ : S →ₐ[R] IsLocalRing.ResidueField R)
    [(RingHom.ker φ).IsPrime] [Algebra.IsSmoothAt R (RingHom.ker φ)] :
    ∃ ψ : S →ₐ[R] R, ∀ s : S, algebraMap R (IsLocalRing.ResidueField R) (ψ s) = φ s := by h77_exact_reverting @_root_.ZInQ.Contrib.CloudR2NeronExistence.Henselian.P2MW.S_HenselianLocalRing_exists_algHom_lift_of_isSmoothAt.solution


end ZInQ.Contrib.CloudR2NeronExistence.Henselian
